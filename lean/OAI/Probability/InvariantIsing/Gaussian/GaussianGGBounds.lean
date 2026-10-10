import OAI.Probability.InvariantIsing.Arrays.PerturbationFeatures

namespace OAI

/-! Gaussian GG estimates retaining the spectral diagonal error. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

omit [Countable X] [MeasurableSingletonClass X] [IsProbabilityMeasure P]
  [∀ ω, IsProbabilityMeasure (ν ω)] in
lemma randomReplicaAverage_const_mul (A : X → ℕ →₀ ℝ) (t c : ℝ)
    {r : ℕ} (D : (Fin r → X) → ℝ) :
    randomReplicaAverage P ν A t (fun σ => c * D σ) =
      c * randomReplicaAverage P ν A t D := by
  unfold randomReplicaAverage
  simp_rw [referenceReplicaMean_const_mul]
  exact integral_const_mul _ _

lemma randomReplicaAverage_add_bounded (hν : Measurable ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    (t : ℝ) {r : ℕ} (D E : (Fin r → X) → ℝ)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hD : ∀ σ, |D σ| ≤ c) (hE : ∀ σ, |E σ| ≤ d) :
    randomReplicaAverage P ν A t (fun σ => D σ + E σ) =
      randomReplicaAverage P ν A t D + randomReplicaAverage P ν A t E := by
  unfold randomReplicaAverage
  calc
    _ = ∫ z : Ω × (ℕ → ℝ),
        referenceReplicaMean (ν z.1) (fun x => t * cylinderField (A x) z.2) D +
        referenceReplicaMean (ν z.1) (fun x => t * cylinderField (A x) z.2) E
          ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
      exact referenceReplicaMean_add_bounded _ _ (hz t) D E hD hE
    _ = _ := integral_add
      (integrable_random_scaled_mean hν A t D hc hD)
      (integrable_random_scaled_mean hν A t E hd hE)

/-- Gaussian integration by parts without imposing a constant diagonal. -/
theorem randomReplicaEnergy_full_identity (hν : Measurable ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    (t : ℝ) {r : ℕ} (D : (Fin (r + 1) → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    randomReplicaEnergy P ν A t D = t *
      (randomReplicaAverage P ν A t (fun σ => D σ *
        (∑ i : Fin (r + 1), cylinderCross (A (σ 0)) (A (σ i)))) -
      (r + 1 : ℕ) * randomReplicaAverage P ν A t
        (fun τ : Fin (r + 1 + 1) → X => D (Fin.tail τ) *
          cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
  have h := joint_countable_cylinder_insertion (P := P) hν
    (fun x => t • A x) A
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t))
    hA D hc hD
  simp only [cylinderField_smul, cylinderCross_smul_right] at h
  have heq : (fun σ : Fin (r + 1) → X =>
      D σ * (∑ i, t * cylinderCross (A (σ 0)) (A (σ i)))) =
      (fun σ => t * (D σ * ∑ i, cylinderCross (A (σ 0)) (A (σ i)))) := by
    funext σ
    rw [← Finset.mul_sum]
    ring
  have hfresh : (fun τ : Fin (r + 1 + 1) → X =>
      D (Fin.tail τ) * (t * cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) =
      (fun τ => t * (D (Fin.tail τ) *
        cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
    funext τ
    ring
  rw [heq, hfresh] at h
  simp_rw [referenceReplicaMean_const_mul] at h
  rw [integral_const_mul, integral_const_mul] at h
  change randomReplicaEnergy P ν A t D = _ at h
  rw [h]
  unfold randomReplicaAverage
  ring

/-- The finite GG error splits into an energy fluctuation and an explicit
covariance of the self-overlap. Spectral self-overlaps are not constant before
adding their separate deterministic perturbations. -/
theorem countable_gaussian_gg_bound_variable_diagonal (hν : Measurable ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    (t b : ℝ) {r : ℕ} (D : (Fin (r + 1) → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A x) z.2 - b|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A x) z.2))
      (P.prod gaussianCoordinates)) :
    |t| * |(r + 1 : ℕ) * randomReplicaAverage P ν A t
        (fun τ : Fin (r + 1 + 1) → X => D (Fin.tail τ) *
          cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))) -
      randomReplicaAverage P ν A t D * randomReplicaAverage P ν A t
        (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0))) -
      randomReplicaAverage P ν A t
        (fun σ => D σ * ∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))| ≤
    2 * c * (∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A x) z.2 - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A x) z.2)
        ∂P.prod gaussianCoordinates) +
    |t| * |randomReplicaAverage P ν A t
        (fun σ => D σ * cylinderCross (A (σ 0)) (A (σ 0))) -
      randomReplicaAverage P ν A t D * randomReplicaAverage P ν A t
        (fun σ : Fin 1 → X => cylinderCross (A (σ 0)) (A (σ 0)))| := by
  let V := randomReplicaAverage P ν A t D
  let U := randomReplicaEnergy P ν A t D
  let M := randomReplicaEnergy P ν A t (fun _ : Fin 1 → X => 1)
  let E := ∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A x) z.2 - b|
    ∂(ν z.1).tilted (fun x => t * cylinderField (A x) z.2)
      ∂P.prod gaussianCoordinates
  let L := randomReplicaAverage P ν A t
    (fun σ => D σ * cylinderCross (A (σ 0)) (A (σ 0)))
  let L₀ := randomReplicaAverage P ν A t
    (fun σ : Fin 1 → X => cylinderCross (A (σ 0)) (A (σ 0)))
  have hEn : 0 ≤ E := integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  have hU : |U - b * V| ≤ c * E := joint_cylinder_energy_covariance_bound hν A hA t b D hc hD hE
  have hM : |M - b| ≤ E := by
    have h := joint_cylinder_energy_covariance_bound hν A hA t b
      (fun _ : Fin (0 + 1) → X => 1) (c := 1) (by norm_num) (fun _ => by norm_num) hE
    change |M - b * randomReplicaAverage P ν A t (fun _ : Fin 1 → X => 1)| ≤ 1 * E at h
    simpa only [randomReplicaAverage_const hν A hA, mul_one, one_mul] using h
  have hV : |V| ≤ c := randomReplicaAverage_abs_le hν A t D hc hD
  have hm : M = t * (L₀ - randomReplicaAverage P ν A t
      (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0)))) := by
    have h := randomReplicaEnergy_full_identity (P := P) (r := 0) hν A hA t
      (fun _ : Fin (0 + 1) → X => 1) (c := 1) (by norm_num) (fun _ => by norm_num)
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_mul, Fin.tail,
      Fin.succ_zero_eq_one, Nat.cast_one, Nat.zero_add] using h
  have hdiag (σ : Fin (r + 1) → X) :
      |D σ * cylinderCross (A (σ 0)) (A (σ 0))| ≤ c * |B| := by
    rw [abs_mul]
    exact mul_le_mul (hD σ) (cylinderCross_bound A hA _ _) (abs_nonneg _) hc
  have hoff (σ : Fin (r + 1) → X) :
      |D σ * ∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ))| ≤ c * (r * |B|) := by
    rw [abs_mul]
    apply mul_le_mul (hD σ) _ (abs_nonneg _) hc
    calc
      _ ≤ ∑ l : Fin r, |cylinderCross (A (σ 0)) (A (σ l.succ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, |B| := Finset.sum_le_sum (fun _ _ => cylinderCross_bound A hA _ _)
      _ = _ := by simp
  have hu : U = t * (L + randomReplicaAverage P ν A t
      (fun σ => D σ * ∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ))) -
      (r + 1 : ℕ) * randomReplicaAverage P ν A t
        (fun τ : Fin (r + 1 + 1) → X => D (Fin.tail τ) *
          cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
    have h := randomReplicaEnergy_full_identity (P := P) hν A hA t D hc hD
    simp only [Fin.sum_univ_succ, mul_add] at h
    rw [randomReplicaAverage_add_bounded hν A hA t _ _
      (mul_nonneg hc (abs_nonneg _)) (by positivity) hdiag hoff] at h
    exact h
  have hr : t * ((r + 1 : ℕ) * randomReplicaAverage P ν A t
      (fun τ : Fin (r + 1 + 1) → X => D (Fin.tail τ) *
        cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))) -
      V * randomReplicaAverage P ν A t
        (fun τ : Fin 2 → X => cylinderCross (A (τ 1)) (A (τ 0))) -
      randomReplicaAverage P ν A t
        (fun σ => D σ * ∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))) =
      M * V - U + t * (L - V * L₀) := by
    rw [hm, hu]
    ring
  rw [← abs_mul]
  change |t * _| ≤ 2 * c * E + |t| * |L - V * L₀|
  rw [hr]
  calc
    _ ≤ |M * V - U| + |t * (L - V * L₀)| := abs_add_le _ _
    _ = |(M - b) * V - (U - b * V)| + |t| * |L - V * L₀| := by
      rw [abs_mul]
      congr 2
      ring
    _ ≤ (|M - b| * |V| + |U - b * V|) + |t| * |L - V * L₀| := by
      exact add_le_add (by
        simpa only [abs_mul] using (abs_sub ((M - b) * V) (U - b * V))) le_rfl
    _ ≤ (E * c + c * E) + |t| * |L - V * L₀| :=
      add_le_add (add_le_add (mul_le_mul hM hV (abs_nonneg _) hEn) hU) le_rfl
    _ = _ := by ring

end InvariantIsing

end

end OAI
