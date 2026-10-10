import OAI.Probability.InvariantIsing.Pressure.RandomCoefficientIBP
import OAI.Probability.InvariantIsing.Arrays.ReplicaCovariance
import OAI.Probability.InvariantIsing.Core.GGErrorAlgebra
import OAI.Probability.IsingPerceptron.JointGGClosure

namespace OAI

/-! GG estimates for Haar-dependent Gaussian perturbation tensors. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Expectation over external disorder and independent Gaussian coordinates. -/
def randomCoefficientAverage (P : Measure Ω) (ν : Ω → Measure X)
    (A : Ω → X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : Ω → (Fin r → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t * cylinderField (A z.1 x) z.2) (D z.1) ∂P.prod gaussianCoordinates

def randomCoefficientEnergy (P : Measure Ω) (ν : Ω → Measure X)
    (A : Ω → X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t * cylinderField (A z.1 x) z.2)
    (fun σ => cylinderField (A z.1 (σ 0)) z.2 * D z.1 σ) ∂P.prod gaussianCoordinates

variable [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

lemma randomCoefficientAverage_abs_le (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (t : ℝ) {r : ℕ} (D : Ω → (Fin r → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) : |randomCoefficientAverage P ν A t D| ≤ c := by
  apply abs_integral_le_const_of_bound
  · simpa only [cylinderField_smul] using
      measurable_randomCoefficient_mean hν (fun ω x => t • A ω x)
        (by simpa only [cylinderField_smul] using hAm.const_mul t) D hDm
  · intro z
    exact referenceReplicaMean_abs_le _ _ _ (measurable_of_countable _) hc (hD z.1)

lemma randomCoefficientAverage_one (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) (r : ℕ) :
    randomCoefficientAverage P ν A t (fun (_ : Ω) (_ : Fin r → X) => 1) = 1 := by
  unfold randomCoefficientAverage
  calc
    _ = ∫ _z : Ω × (ℕ → ℝ), (1 : ℝ) ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [randomCoefficient_all_exp_ae (P := P) hν A hAm hA] with z hz
      exact referenceReplicaMean_const _ _ (hz t) r 1
    _ = 1 := by simp

lemma randomCoefficientAverage_add_bounded (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t : ℝ) {r : ℕ} (D E : Ω → (Fin r → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) (hEm : Measurable (Function.uncurry E))
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hD : ∀ ω σ, |D ω σ| ≤ c) (hE : ∀ ω σ, |E ω σ| ≤ d) :
    randomCoefficientAverage P ν A t (fun ω σ => D ω σ + E ω σ) =
      randomCoefficientAverage P ν A t D + randomCoefficientAverage P ν A t E := by
  have ht : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
      cylinderField (t • A p.1.1 p.2) p.1.2) := by
    simpa only [cylinderField_smul] using hAm.const_mul t
  have hiD := integrable_randomCoefficient_mean (P := P) hν
    (fun ω x => t • A ω x) ht D hDm hc hD
  have hiE := integrable_randomCoefficient_mean (P := P) hν
    (fun ω x => t • A ω x) ht E hEm hd hE
  simp only [cylinderField_smul] at hiD hiE
  unfold randomCoefficientAverage
  calc
    _ = ∫ z : Ω × (ℕ → ℝ),
        referenceReplicaMean (ν z.1) (fun x => t * cylinderField (A z.1 x) z.2) (D z.1) +
        referenceReplicaMean (ν z.1) (fun x => t * cylinderField (A z.1 x) z.2) (E z.1)
          ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [randomCoefficient_all_exp_ae (P := P) hν A hAm hA] with z hz
      exact referenceReplicaMean_add_bounded _ _ (hz t) _ _ (hD z.1) (hE z.1)
    _ = _ := integral_add hiD hiE

/-- Conditional Gaussian integration by parts, with the diagonal retained. -/
theorem randomCoefficientEnergy_full_identity (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hcross : Measurable (fun p : Ω × (X × X) => cylinderCross (A p.1 p.2.1) (A p.1 p.2.2)))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) :
    randomCoefficientEnergy P ν A t D = t *
      (randomCoefficientAverage P ν A t (fun ω σ => D ω σ *
        (∑ i : Fin (r + 1), cylinderCross (A ω (σ 0)) (A ω (σ i)))) -
      (r + 1 : ℕ) * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin (r + 1 + 1) → X) => D ω (Fin.tail τ) *
          cylinderCross (A ω ((Fin.tail τ) 0)) (A ω (τ 0)))) := by
  have h := joint_randomCoefficient_cylinder_insertion (P := P) hν
    (fun ω x => t • A ω x) A
    (by simpa only [cylinderField_smul] using hAm.const_mul t) hAm
    (by simpa only [cylinderCross_smul_right] using hcross.const_mul t)
    (fun ω x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA ω x) (sq_nonneg t))
    hA D hDm hc hD
  simp only [cylinderField_smul, cylinderCross_smul_right] at h
  have heq (ω : Ω) : (fun σ : Fin (r + 1) → X =>
      D ω σ * (∑ i, t * cylinderCross (A ω (σ 0)) (A ω (σ i)))) =
      (fun σ => t * (D ω σ * ∑ i, cylinderCross (A ω (σ 0)) (A ω (σ i)))) := by
    funext σ
    rw [← Finset.mul_sum]
    ring
  have hfresh (ω : Ω) : (fun τ : Fin (r + 1 + 1) → X =>
      D ω (Fin.tail τ) * (t * cylinderCross (A ω ((Fin.tail τ) 0)) (A ω (τ 0)))) =
      (fun τ => t * (D ω (Fin.tail τ) *
        cylinderCross (A ω ((Fin.tail τ) 0)) (A ω (τ 0)))) := by
    funext τ
    ring
  simp_rw [heq, hfresh, referenceReplicaMean_const_mul] at h
  rw [integral_const_mul, integral_const_mul] at h
  change randomCoefficientEnergy P ν A t D = _ at h
  rw [h]
  unfold randomCoefficientAverage
  ring

/-- Energy fluctuation bounds remain valid for Haar-dependent tensors and
Haar-dependent replica tests. -/
theorem randomCoefficient_energy_covariance_bound (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t b : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A z.1 x) z.2 - b|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2))
      (P.prod gaussianCoordinates)) :
    |randomCoefficientEnergy P ν A t D - b * randomCoefficientAverage P ν A t D| ≤
      c * (∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A z.1 x) z.2 - b|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
          ∂P.prod gaussianCoordinates) := by
  have ht : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
      cylinderField (t • A p.1.1 p.2) p.1.2) := by
    simpa only [cylinderField_smul] using hAm.const_mul t
  have hiU := integrable_randomCoefficient_insertion (P := P) hν
    (fun ω x => t • A ω x) A ht hAm
    (fun ω x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA ω x) (sq_nonneg t))
    hA D hDm hc hD
  have hiV := integrable_randomCoefficient_mean (P := P) hν
    (fun ω x => t • A ω x) ht D hDm hc hD
  simp only [cylinderField_smul] at hiU hiV
  have he := randomCoefficient_all_exp_ae (P := P) hν A hAm hA
  have hY : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => cylinderField (A z.1 x) z.2)
        ((ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)) := by
    filter_upwards [he] with z hz
    exact (memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1 : NNReal)).integrable
      (by norm_num)
  exact random_replica_energy_covariance_bound (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (H := fun p => t * cylinderField (A p.1.1 p.2) p.1.2)
    (Y := fun p => cylinderField (A p.1.1 p.2) p.1.2)
    (fun p => D p.1.1 p.2)
    (hDm.comp (measurable_fst.fst.prodMk measurable_snd)) hc (fun z => hD z.1) b
    (he.mono fun _ hz => hz t) hY hiU hiV hE

/-- The finite GG comparison for the actual type of perturbations used here:
both coefficients and tests may depend on the external Haar disorder, and
the spectral self-overlap covariance remains an explicit error. -/
theorem randomCoefficient_gaussian_gg_bound (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hcross : Measurable (fun p : Ω × (X × X) => cylinderCross (A p.1 p.2.1) (A p.1 p.2.2)))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t b : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A z.1 x) z.2 - b|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2))
      (P.prod gaussianCoordinates)) :
    |t| * |(r + 1 : ℕ) * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin (r + 1 + 1) → X) => D ω (Fin.tail τ) *
          cylinderCross (A ω ((Fin.tail τ) 0)) (A ω (τ 0))) -
      randomCoefficientAverage P ν A t D * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin 2 → X) => cylinderCross (A ω (τ 1)) (A ω (τ 0))) -
      randomCoefficientAverage P ν A t
        (fun ω σ => D ω σ * ∑ l : Fin r, cylinderCross (A ω (σ 0)) (A ω (σ l.succ)))| ≤
    2 * c * (∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A z.1 x) z.2 - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
        ∂P.prod gaussianCoordinates) +
    |t| * |randomCoefficientAverage P ν A t
        (fun ω σ => D ω σ * cylinderCross (A ω (σ 0)) (A ω (σ 0))) -
      randomCoefficientAverage P ν A t D * randomCoefficientAverage P ν A t
        (fun ω (σ : Fin 1 → X) => cylinderCross (A ω (σ 0)) (A ω (σ 0)))| := by
  let V := randomCoefficientAverage P ν A t D
  let U := randomCoefficientEnergy P ν A t D
  let M := randomCoefficientEnergy P ν A t (fun (_ : Ω) (_ : Fin 1 → X) => 1)
  let E := ∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A z.1 x) z.2 - b|
    ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
      ∂P.prod gaussianCoordinates
  let L := randomCoefficientAverage P ν A t
    (fun ω σ => D ω σ * cylinderCross (A ω (σ 0)) (A ω (σ 0)))
  let L₀ := randomCoefficientAverage P ν A t
    (fun ω (σ : Fin 1 → X) => cylinderCross (A ω (σ 0)) (A ω (σ 0)))
  have hEn : 0 ≤ E := integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  have hU : |U - b * V| ≤ c * E :=
    randomCoefficient_energy_covariance_bound hν A hAm hA t b D hDm hc hD hE
  have hM : |M - b| ≤ E := by
    have h := randomCoefficient_energy_covariance_bound (P := P) hν A hAm hA t b
      (fun (_ : Ω) (_ : Fin (0 + 1) → X) => 1) measurable_const (c := 1) (by norm_num)
      (fun _ _ => by norm_num) hE
    change |M - b * randomCoefficientAverage P ν A t (fun (_ : Ω) (_ : Fin 1 → X) => 1)| ≤ 1 * E at h
    simpa only [randomCoefficientAverage_one hν A hAm hA, mul_one, one_mul] using h
  have hV : |V| ≤ c := randomCoefficientAverage_abs_le hν A hAm t D hDm hc hD
  have hm : M = t * (L₀ - randomCoefficientAverage P ν A t
      (fun ω (τ : Fin 2 → X) => cylinderCross (A ω (τ 1)) (A ω (τ 0)))) := by
    have h := randomCoefficientEnergy_full_identity (P := P) (r := 0) hν A hAm hcross hA t
      (fun (_ : Ω) (_ : Fin (0 + 1) → X) => 1) measurable_const (c := 1) (by norm_num)
      (fun _ _ => by norm_num)
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_mul, Fin.tail,
      Fin.succ_zero_eq_one, Nat.cast_one, Nat.zero_add] using h
  have hdiagM : Measurable (Function.uncurry (fun ω (σ : Fin (r + 1) → X) =>
      D ω σ * cylinderCross (A ω (σ 0)) (A ω (σ 0)))) := by
    have hp : Measurable (fun p : Ω × (Fin (r + 1) → X) => (p.1, (p.2 0, p.2 0))) :=
      measurable_fst.prodMk
        (((measurable_pi_apply 0).comp measurable_snd).prodMk
          ((measurable_pi_apply 0).comp measurable_snd))
    exact hDm.mul (hcross.comp hp)
  have hoffM : Measurable (Function.uncurry (fun ω (σ : Fin (r + 1) → X) =>
      D ω σ * ∑ l : Fin r, cylinderCross (A ω (σ 0)) (A ω (σ l.succ)))) := by
    apply hDm.mul
    apply Finset.measurable_sum
    intro l _
    have hp : Measurable (fun p : Ω × (Fin (r + 1) → X) => (p.1, (p.2 0, p.2 l.succ))) :=
      measurable_fst.prodMk
        (((measurable_pi_apply 0).comp measurable_snd).prodMk
          ((measurable_pi_apply l.succ).comp measurable_snd))
    exact hcross.comp hp
  have hdiag (ω : Ω) (σ : Fin (r + 1) → X) :
      |D ω σ * cylinderCross (A ω (σ 0)) (A ω (σ 0))| ≤ c * |B| := by
    rw [abs_mul]
    exact mul_le_mul (hD ω σ) (cylinderCross_bound (A ω) (hA ω) _ _) (abs_nonneg _) hc
  have hoff (ω : Ω) (σ : Fin (r + 1) → X) :
      |D ω σ * ∑ l : Fin r, cylinderCross (A ω (σ 0)) (A ω (σ l.succ))| ≤ c * (r * |B|) := by
    rw [abs_mul]
    apply mul_le_mul (hD ω σ) _ (abs_nonneg _) hc
    calc
      _ ≤ ∑ l : Fin r, |cylinderCross (A ω (σ 0)) (A ω (σ l.succ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, |B| := Finset.sum_le_sum (fun _ _ => cylinderCross_bound (A ω) (hA ω) _ _)
      _ = _ := by simp
  have hu : U = t * (L + randomCoefficientAverage P ν A t
      (fun ω σ => D ω σ * ∑ l : Fin r, cylinderCross (A ω (σ 0)) (A ω (σ l.succ))) -
      (r + 1 : ℕ) * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin (r + 1 + 1) → X) => D ω (Fin.tail τ) *
          cylinderCross (A ω ((Fin.tail τ) 0)) (A ω (τ 0)))) := by
    have h := randomCoefficientEnergy_full_identity (P := P) hν A hAm hcross hA t D hDm hc hD
    simp only [Fin.sum_univ_succ, mul_add] at h
    rw [randomCoefficientAverage_add_bounded hν A hAm hA t _ _ hdiagM hoffM
      (mul_nonneg hc (abs_nonneg _)) (by positivity) hdiag hoff] at h
    exact h
  exact gaussianGG_of_energy_identities hEn hU hM hV hu hm

/-- Gaussian mean logpartition bounds remain valid when the coefficient
vectors depend on the external rotation disorder. -/
lemma randomCoefficient_cgf_mean_bounds (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    0 ≤ (∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates) ∧
    (∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates) ≤ t ^ 2 * B / 2 := by
  have hi := integrable_randomCoefficient_cgf (P := P) hν A hAm hA t
  rw [integral_prod _ hi]
  refine ⟨integral_nonneg (fun ω => (cylinder_cgf_mean_bounds (ν ω) (A ω) (hA ω) t).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, t ^ 2 * B / 2 ∂P := integral_mono hi.integral_prod_left
      (integrable_const _) (fun ω => (cylinder_cgf_mean_bounds (ν ω) (A ω) (hA ω) t).2)
    _ = _ := by simp

/-- The local-minimum fluctuation estimate applies to the actual
Haar-dependent Gaussian fields, rather than requiring fixed coefficients. -/
theorem randomCoefficient_energy_at_minimum (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Set.Icc (v - s) (v + s),
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) v
        ∂P.prod gaussianCoordinates) + c * (v - a) ^ 2 ≤
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
        ∂P.prod gaussianCoordinates) + c * (t - a) ^ 2)
    (hconc : ∀ t ∈ ({v - s, v, v + s} : Set ℝ),
      (∫ z : Ω × (ℕ → ℝ), |cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t -
        (∫ z' : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z'.1 x) z'.2) (ν z'.1) t
          ∂P.prod gaussianCoordinates)| ∂P.prod gaussianCoordinates) ≤ δ) :
    let E := fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A z.1 x) z.2 - 2 * c * (v - a)|
        ∂(ν z.1).tilted (fun x => v * cylinderField (A z.1 x) z.2)
    Integrable E (P.prod gaussianCoordinates) ∧
      (∫ z, E z ∂P.prod gaussianCoordinates) ≤ (2 * c + K ^ 2) / (2 * K) + c * s + 4 * δ / s := by
  exact expected_tilted_energy_at_minimum (μ := P.prod gaussianCoordinates)
    (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (Y := fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2)
    (hν.comp measurable_fst) hAm hs hK
    (randomCoefficient_all_exp_ae hν A hAm hA)
    (integrable_randomCoefficient_cgf hν A hAm hA) hmin hconc

end InvariantIsing

end

end OAI
