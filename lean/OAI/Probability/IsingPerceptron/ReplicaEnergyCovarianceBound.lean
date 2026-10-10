import Mathlib
import OAI.Probability.IsingPerceptron.ChildLabel
import OAI.Probability.IsingPerceptron.ConvexDerivativeFluctuation

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma replica_energy_covariance_bound {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ} (hY : Integrable Y ν)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) (hDm : Measurable D)
    {c : ℝ} (_hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) (b : ℝ) :
    |(∫ σ, Y (σ 0)*D σ ∂Measure.pi (fun _ : Fin (r+1) => ν)) -
      b*(∫ σ, D σ ∂Measure.pi (fun _ : Fin (r+1) => ν))| ≤
        c*(∫ x, |Y x-b| ∂ν) := by
  let ρ := Measure.pi (fun _ : Fin (r+1) => ν)
  have hDi : Integrable D ρ := integrable_of_measurable_abs_le hDm hD
  have hYi : Integrable (fun σ : Fin (r+1) → X => Y (σ 0)) ρ := integrable_comp_eval hY
  have hmul : Integrable (fun σ : Fin (r+1) → X => Y (σ 0)*D σ) ρ :=
    hYi.mul_bdd hDm.aestronglyMeasurable (ae_of_all _ (fun σ => by simpa using hD σ))
  have hsub : Integrable (fun σ : Fin (r+1) → X => (Y (σ 0)-b)*D σ) ρ :=
    (hYi.sub (integrable_const _)).mul_bdd hDm.aestronglyMeasurable
      (ae_of_all _ (fun σ => by simpa using hD σ))
  have habs : Integrable (fun σ : Fin (r+1) → X => |Y (σ 0)-b|) ρ :=
    (hYi.sub (integrable_const _)).abs
  calc
    _ = |∫ σ, (Y (σ 0)-b)*D σ ∂ρ| := by
      rw [show (fun σ : Fin (r+1) → X => (Y (σ 0)-b)*D σ) =
        (fun σ => Y (σ 0)*D σ-b*D σ) from by funext σ; ring,
        integral_sub hmul (hDi.const_mul b),integral_const_mul]
    _ ≤ ∫ σ, |(Y (σ 0)-b)*D σ| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ σ, c*|Y (σ 0)-b| ∂ρ := by
      apply integral_mono hsub.abs (habs.const_mul c)
      intro σ
      dsimp only
      rw [abs_mul,mul_comm c]
      exact mul_le_mul_of_nonneg_left (hD σ) (abs_nonneg _)
    _ = c*(∫ x, |Y x-b| ∂ν) := by
      rw [integral_const_mul]
      congr 1
      exact (measurePreserving_eval (fun _ : Fin (r+1) => ν) 0).hasLaw.integral_comp
        ((hY.sub (integrable_const _)).abs.aestronglyMeasurable)

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cylinder_norm_smul (a : ℕ →₀ ℝ) (t : ℝ) :
    (t • a).sum (fun _ c => c^2) = t^2*a.sum (fun _ c => c^2) := by
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [mul_pow,Finsupp.sum]
  rw [Finset.mul_sum]

lemma cylinderCross_smul_right (a b : ℕ →₀ ℝ) (t : ℝ) :
    cylinderCross a (t • b) = t*cylinderCross a b := by
  simp only [cylinderCross,Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma joint_cylinder_energy_covariance_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (t b : ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x, |cylinderField (A x) z.2-b|
      ∂(ν z.1).tilted (fun x => t*cylinderField (A x) z.2)) (P.prod gaussianCoordinates)) :
    |(∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => t*cylinderField (A x) z.2) (fun σ => cylinderField (A (σ 0)) z.2*D σ)
      ∂P.prod gaussianCoordinates) -
      b*(∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
        (fun x => t*cylinderField (A x) z.2) D ∂P.prod gaussianCoordinates)| ≤
    c*(∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A x) z.2-b|
      ∂(ν z.1).tilted (fun x => t*cylinderField (A x) z.2) ∂P.prod gaussianCoordinates) := by
  let μ := P.prod gaussianCoordinates
  let H := fun z : Ω × (ℕ → ℝ) => fun x => t*cylinderField (A x) z.2
  let U := fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1) (H z)
    (fun σ => cylinderField (A (σ 0)) z.2*D σ)
  let V := fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1) (H z) D
  have hU : Integrable U μ := by
    have h := integrable_joint_cylinder_insertion (P := P) hν (fun x => t • A x) A
      (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)) hA D hc hD
    simpa only [cylinderField_smul] using h
  have hV : Integrable V μ := by
    have h := integrable_joint_cylinder_mean (P := P) hν (fun x => t • A x) D hc hD
    simpa only [cylinderField_smul] using h
  have hb : ∀ᵐ z ∂μ, |U z-b*V z| ≤ c*(∫ x, |cylinderField (A x) z.2-b|
      ∂(ν z.1).tilted (H z)) := by
    filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
    have : IsProbabilityMeasure ((ν z.1).tilted (H z)) := isProbabilityMeasure_tilted (hz t)
    have hi : Integrable (fun x => cylinderField (A x) z.2) ((ν z.1).tilted (H z)) :=
      (memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1:NNReal)).integrable (by norm_num)
    dsimp [U,V]
    rw [referenceReplicaMean_eq_tilted _ _ (hz t),referenceReplicaMean_eq_tilted _ _ (hz t)]
    exact replica_energy_covariance_bound hi D (measurable_of_countable _) hc hD b
  change |(∫ z, U z ∂μ)-b*(∫ z, V z ∂μ)| ≤ _
  rw [← integral_const_mul,← integral_sub hU (hV.const_mul b)]
  exact abs_integral_le_integral_abs.trans
    ((integral_mono_ae (hU.sub (hV.const_mul b)).abs (hE.const_mul c) hb).trans_eq
      (integral_const_mul _ _))

lemma referenceReplicaMean_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) (c : ℝ) :
    referenceReplicaMean ν H (fun σ => c*D σ) = c*referenceReplicaMean ν H D := by
  unfold referenceReplicaMean
  rw [show (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*(c*D σ)) =
    (fun σ => c*(Real.exp (∑ i, H (σ i))*D σ)) from by funext σ; ring,
    integral_const_mul]
  ring

lemma referenceReplicaMean_const {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) (c : ℝ) :
    referenceReplicaMean ν H (fun _ : Fin r → X => c) = c := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he]
  simp

lemma referenceReplicaMean_add_bounded {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (D E : (Fin r → X) → ℝ) {c d : ℝ}
    (hD : ∀ σ, |D σ| ≤ c) (hE : ∀ σ, |E σ| ≤ d) :
    referenceReplicaMean ν H (fun σ => D σ+E σ) =
      referenceReplicaMean ν H D+referenceReplicaMean ν H E := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he,referenceReplicaMean_eq_tilted ν H he,
    referenceReplicaMean_eq_tilted ν H he]
  exact integral_add (integrable_of_measurable_abs_le (measurable_of_countable _) hD)
    (integrable_of_measurable_abs_le (measurable_of_countable _) hE)

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

lemma cylinderCross_bound {X : Type*} (A : X → ℕ →₀ ℝ) {B : ℝ}
    (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B) (x y : X) :
    |cylinderCross (A x) (A y)| ≤ |B| := by
  calc
    _ ≤ ((A x).sum (fun _ c => c^2)+(A y).sum (fun _ c => c^2))/2 := abs_cylinderCross_le _ _
    _ ≤ |B| := by linarith [hA x,hA y,le_abs_self B]

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

def randomReplicaAverage (P : Measure Ω) (ν : Ω → Measure X) (A : X → ℕ →₀ ℝ)
    (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t*cylinderField (A x) z.2) D ∂P.prod gaussianCoordinates

def randomReplicaEnergy (P : Measure Ω) (ν : Ω → Measure X) (A : X → ℕ →₀ ℝ)
    (t : ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t*cylinderField (A x) z.2) (fun σ => cylinderField (A (σ 0)) z.2*D σ)
    ∂P.prod gaussianCoordinates

lemma integrable_random_scaled_mean [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => t*cylinderField (A x) z.2) D) (P.prod gaussianCoordinates) := by
  simpa only [cylinderField_smul] using
    integrable_joint_cylinder_mean (P := P) hν (fun x => t • A x) D hc hD

lemma randomReplicaAverage_const [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (t : ℝ) (r : ℕ) (c : ℝ) : randomReplicaAverage P ν A t (fun _ : Fin r → X => c) = c := by
  unfold randomReplicaAverage
  calc
    _ = ∫ _z : Ω × (ℕ → ℝ), c ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
      exact referenceReplicaMean_const _ _ (hz t) r c
    _ = c := by simp

lemma randomReplicaAverage_abs_le [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    |randomReplicaAverage P ν A t D| ≤ c := by
  apply abs_integral_le_const_of_bound
  · simpa only [cylinderField_smul] using measurable_random_cylinder_mean hν (fun x => t • A x) D
  · intro z
    exact referenceReplicaMean_abs_le _ _ _ (measurable_of_countable _) hc hD

theorem randomReplicaEnergy_identity [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B d : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (hdiag : ∀ x, cylinderCross (A x) (A x) = d) (t : ℝ)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    randomReplicaEnergy P ν A t D = t*(d*randomReplicaAverage P ν A t D +
      randomReplicaAverage P ν A t (fun σ => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))) -
      (r+1 : ℕ)*randomReplicaAverage P ν A t
        (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
  let μ := P.prod gaussianCoordinates
  let H := fun z : Ω × (ℕ → ℝ) => fun x => t*cylinderField (A x) z.2
  let E := fun σ : Fin (r+1) → X => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))
  have hE (σ : Fin (r+1) → X) : |E σ| ≤ c*((r:ℝ)*|B|) := by
    dsimp [E]
    rw [abs_mul]
    apply mul_le_mul (hD σ) _ (abs_nonneg _) hc
    calc
      _ ≤ ∑ l : Fin r, |cylinderCross (A (σ 0)) (A (σ l.succ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, |B| := Finset.sum_le_sum (fun _ _ => cylinderCross_bound A hA _ _)
      _ = _ := by simp
  have hV := integrable_random_scaled_mean (P := P) hν A t D hc hD
  have hW := integrable_random_scaled_mean (P := P) hν A t E (by positivity) hE
  have first : (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (H z)
      (fun σ => D σ*(∑ i : Fin (r+1), t*cylinderCross (A (σ 0)) (A (σ i)))) ∂μ) =
      t*(d*randomReplicaAverage P ν A t D+randomReplicaAverage P ν A t E) := by
    calc
      _ = ∫ z : Ω × (ℕ → ℝ), t*(d*referenceReplicaMean (ν z.1) (H z) D+
          referenceReplicaMean (ν z.1) (H z) E) ∂μ := by
        apply integral_congr_ae
        filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
        have heq : (fun σ : Fin (r+1) → X => D σ*(∑ i, t*cylinderCross (A (σ 0)) (A (σ i)))) =
            (fun σ => t*(d*D σ+E σ)) := by
          funext σ
          rw [Fin.sum_univ_succ,hdiag,← Finset.mul_sum]
          dsimp [E]
          ring
        rw [heq,referenceReplicaMean_const_mul,
          referenceReplicaMean_add_bounded _ _ (hz t) _ _
            (fun σ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD σ) (abs_nonneg d)) hE,
          referenceReplicaMean_const_mul]
      _ = _ := by
        rw [integral_const_mul,integral_add (hV.const_mul d) hW,integral_const_mul]
        rfl
  have h := joint_countable_cylinder_insertion (P := P) hν (fun x => t • A x) A
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)) hA D hc hD
  simp only [cylinderField_smul,cylinderCross_smul_right] at h
  have hfresh : (fun (z : Ω × (ℕ → ℝ)) => referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))))) =
    (fun z : Ω × (ℕ → ℝ) => t*referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
    funext z
    rw [show (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) =
      (fun τ => t*(D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) from by funext τ; ring,
      referenceReplicaMean_const_mul]
  change randomReplicaEnergy P ν A t D = _ at h
  change (∫ z, referenceReplicaMean (ν z.1) (H z) _ ∂μ) = _ at first
  rw [first,hfresh,integral_const_mul] at h
  rw [h]
  dsimp [E,randomReplicaAverage,μ,H]
  ring

end IsingPerceptron

namespace IsingPerceptron

theorem countable_gaussian_gg_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B d : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (hdiag : ∀ x, cylinderCross (A x) (A x) = d) (t b : ℝ)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x, |cylinderField (A x) z.2-b|
      ∂(ν z.1).tilted (fun x => t*cylinderField (A x) z.2)) (P.prod gaussianCoordinates)) :
    |t| * |(r+1 : ℕ)*randomReplicaAverage P ν A t
        (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))) -
      randomReplicaAverage P ν A t D * randomReplicaAverage P ν A t
        (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0))) -
      randomReplicaAverage P ν A t
        (fun σ => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ))))| ≤
    2*c*(∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A x) z.2-b|
      ∂(ν z.1).tilted (fun x => t*cylinderField (A x) z.2) ∂P.prod gaussianCoordinates) := by
  let V := randomReplicaAverage P ν A t D
  let U := randomReplicaEnergy P ν A t D
  let M := randomReplicaEnergy P ν A t (fun _ : Fin 1 → X => 1)
  let E := ∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A x) z.2-b|
    ∂(ν z.1).tilted (fun x => t*cylinderField (A x) z.2) ∂P.prod gaussianCoordinates
  have hEn : 0 ≤ E := integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  have hU : |U-b*V| ≤ c*E := joint_cylinder_energy_covariance_bound hν A hA t b D hc hD hE
  have hM : |M-b| ≤ E := by
    have h := joint_cylinder_energy_covariance_bound hν A hA t b
      (fun _ : Fin (0+1) → X => 1) (c := 1) (by norm_num) (fun _ => by norm_num) hE
    change |M-b*randomReplicaAverage P ν A t (fun _ : Fin 1 → X => 1)| ≤ 1*E at h
    simpa only [randomReplicaAverage_const hν A hA,mul_one,one_mul] using h
  have hV : |V| ≤ c := randomReplicaAverage_abs_le hν A t D hc hD
  have hm : M = t*(d-randomReplicaAverage P ν A t
      (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0)))) := by
    have h := randomReplicaEnergy_identity (P := P) hν A hA hdiag t (fun _ : Fin (0+1) → X => 1)
      (c := 1) (by norm_num) (fun _ => by norm_num)
    simpa only [Fin.sum_univ_zero,mul_zero,one_mul,Fin.tail,Fin.succ_zero_eq_one,
      randomReplicaAverage_const hν A hA,mul_one,add_zero,Nat.cast_one, Nat.zero_add] using h
  have hu := randomReplicaEnergy_identity (P := P) hν A hA hdiag t D hc hD
  have hr : t*((r+1 : ℕ)*randomReplicaAverage P ν A t
        (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))) -
      randomReplicaAverage P ν A t D * randomReplicaAverage P ν A t
        (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0))) -
      randomReplicaAverage P ν A t
        (fun σ => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ))))) = M*V-U := by
    rw [hm]
    dsimp only [U,V]
    rw [hu]
    ring
  rw [← abs_mul,hr]
  calc
    _ = |(M-b)*V-(U-b*V)| := by congr 1; ring
    _ ≤ |(M-b)*V|+|U-b*V| := abs_sub _ _
    _ = |M-b| * |V|+|U-b*V| := by rw [abs_mul]
    _ ≤ E*c+c*E := add_le_add (mul_le_mul hM hV (abs_nonneg _) hEn) hU
    _ = _ := by dsimp [E]; ring

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

def featureCoefficients {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) : ℕ →₀ ℝ :=
  ∑ i, Finsupp.single (tag i) (c i)

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma featureCoefficients_variance {I : Type*} [Fintype I]
    (t : I → ℕ) (ht : Function.Injective t) (a : I → ℝ) :
    (featureCoefficients t a).sum (fun _ c => c^2) = ∑ i, (a i)^2 := by
  rw [← cylinderCross_self,featureCoefficients_diagonal t t (fun _ _ h => ht h)]
  simp [pow_two]

def labeledAddress : (n : ℕ) → LabeledLeaf n → List ChildLabel
  | 0, _ => []
  | n+1, v => v.1 :: labeledAddress n v.2

def labeledCommonDepth : (n : ℕ) → LabeledLeaf n → LabeledLeaf n → ℕ
  | 0, _, _ => 0
  | n+1, v, w => if v.1 = w.1 then labeledCommonDepth n v.2 w.2+1 else 0

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

lemma labeledCommonDepth_le (n : ℕ) (v w : LabeledLeaf n) : labeledCommonDepth n v w ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    dsimp only [labeledCommonDepth]
    split_ifs
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true,ih]

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

instance labeledLeafEncodable (n : ℕ) : Encodable (LabeledLeaf n) := Encodable.ofCountable _

def treeFeatureTag {J : Type*} [Encodable J] (n : ℕ) (v : LabeledLeaf n)
    (i : Fin (n+1) × J) : ℕ :=
  Encodable.encode (i.1.1, (labeledAddress n v).take i.1, i.2)

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma treeFeatureTag_injective {J : Type*} [Encodable J] (n : ℕ) (v : LabeledLeaf n) :
    Function.Injective (treeFeatureTag (J := J) n v) := by
  intro i j h
  exact ((treeFeatureTag_cross n v v i j).mp h).1

def treeFieldCoefficients {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v : LabeledLeaf n) (a : Fin (n+1) → ℝ) (c : J → ℝ) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag n v) (fun i => a i.1*c i.2)

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true]; ring
  · simp only [h,ite_false,zero_mul]

def pathIncrement (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => q 0
  | i+1 => q (i+1)-q i

def pathAmplitude (q : ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt (pathIncrement q i)

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

def tensorFeature {J : Type*} [Fintype J] (p : ℕ) (x : J → ℝ) (i : Fin p → J) : ℝ :=
  ∏ d, x (i d)

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

def spinCoordinate {N : ℕ} (x : Spin N) (i : Fin N) : ℝ :=
  spinValue (x i) / Real.sqrt (N : ℝ)

lemma spinValue_sq (x : Fin 2) : spinValue x ^ 2 = 1 := by
  simp only [spinValue]; split_ifs <;> norm_num

lemma spinCoordinate_cross {N : ℕ} (x y : Spin N) :
    (∑ i, spinCoordinate x i * spinCoordinate y i) = spinOverlap x y := by
  simp only [spinCoordinate,div_mul_div_comm,← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N),← Finset.sum_div,spinOverlap]

lemma spinOverlap_self {N : ℕ} (hN : 0 < N) (x : Spin N) : spinOverlap x x = 1 := by
  simp only [spinOverlap,← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hN.ne')

def treeOverlap (n : ℕ) (v w : LabeledLeaf n) : ℝ :=
  (labeledCommonDepth n v w : ℝ) / (n+1 : ℕ)

def monomialPath (n d : ℕ) (i : ℕ) : ℝ := ((i : ℝ) / (n+1 : ℕ)) ^ d

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

def monomialCoefficients {N : ℕ} (n p d : ℕ) (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n s.2 (fun i => pathAmplitude (monomialPath n d) i)
    (tensorFeature p (spinCoordinate s.1))

lemma monomialCoefficients_cross {N : ℕ} (n p d : ℕ)
    (s t : Spin N × LabeledLeaf n) :
    cylinderCross (monomialCoefficients n p d s) (monomialCoefficients n p d t) =
      spinOverlap s.1 t.1 ^ p * treeOverlap n s.2 t.2 ^ d := by
  unfold monomialCoefficients
  rw [treeField_path_cross n s.2 t.2 (monomialPath_monotone n d)
    (monomialPath_nonneg n d 0),tensorFeature_cross,spinCoordinate_cross]
  exact mul_comm _ _

lemma monomialCoefficients_variance {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) = monomialPath n d n := by
  rw [← cylinderCross_self,monomialCoefficients_cross,spinOverlap_self hN,one_pow,one_mul]
  simp only [treeOverlap,labeledCommonDepth_self,monomialPath]

lemma monomialCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) ≤ 1 := by
  rw [monomialCoefficients_variance hN]
  exact monomialPath_diag_le_one _ _

lemma gaussian_pullback_measurePreserving {ι : Type*} (tag : ι → ℕ)
    (ht : Function.Injective tag) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i => g (tag i)) gaussianCoordinates
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp ht).map_fun_eq_infinitePi_map (fun _ => by fun_prop)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

end IsingPerceptron

end

end OAI
