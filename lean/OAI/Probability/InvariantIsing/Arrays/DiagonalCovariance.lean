import OAI.Probability.InvariantIsing.Pressure.RandomCoefficientGG

namespace OAI

/-! Control of the finite spectral GG diagonal error by its actual L1 deviation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

lemma randomCoefficient_bounded_observable_covariance (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t b : ℝ) (Y : Ω → X → ℝ) (hYm : Measurable (Function.uncurry Y))
    {K : ℝ} (hK : 0 ≤ K) (hYb : ∀ ω x, |Y ω x| ≤ K)
    {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) :
    let E := fun z : Ω × (ℕ → ℝ) => ∫ x, |Y z.1 x - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
    Integrable E (P.prod gaussianCoordinates) ∧
      |randomCoefficientAverage P ν A t (fun ω σ => Y ω (σ 0) * D ω σ) -
        b * randomCoefficientAverage P ν A t D| ≤
        c * ∫ z, E z ∂P.prod gaussianCoordinates := by
  have hYm' : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => Y p.1.1 p.2) :=
    hYm.comp (measurable_fst.fst.prodMk measurable_snd)
  have he := randomCoefficient_all_exp_ae (P := P) hν A hAm hA
  have hdev (ω : Ω) (x : X) : |Y ω x - b| ≤ K + |b| :=
    (abs_sub _ _).trans (add_le_add (hYb ω x) le_rfl)
  have hEm := measurable_random_tilted_integral (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hAm.const_mul t) (hYm'.sub_const b |>.abs)
  have hEi : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x, |Y z.1 x - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2))
      (P.prod gaussianCoordinates) := by
    apply (integrable_const (K + |b|)).mono' hEm.aestronglyMeasurable
    filter_upwards [he] with z hz
    have : IsProbabilityMeasure ((ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)) :=
      isProbabilityMeasure_tilted (hz t)
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    calc
      _ ≤ ∫ _x, K + |b| ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2) :=
        integral_mono
          (integrable_of_measurable_abs_le (measurable_of_countable _)
            (fun x => by simpa only [abs_abs] using hdev z.1 x))
          (integrable_const _) (hdev z.1)
      _ = _ := by simp
  have hYi : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (Y z.1) ((ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)) := by
    filter_upwards [he] with z hz
    have : IsProbabilityMeasure ((ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)) :=
      isProbabilityMeasure_tilted (hz t)
    exact integrable_of_measurable_abs_le (measurable_of_countable _) (hYb z.1)
  have ht : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
      cylinderField (t • A p.1.1 p.2) p.1.2) := by
    simpa only [cylinderField_smul] using hAm.const_mul t
  have hYDm : Measurable (Function.uncurry (fun ω (σ : Fin (r + 1) → X) =>
      Y ω (σ 0) * D ω σ)) := by
    have hp : Measurable (fun p : Ω × (Fin (r + 1) → X) => (p.1, p.2 0)) :=
      measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
    exact (hYm.comp hp).mul hDm
  have hiU := integrable_randomCoefficient_mean (P := P) hν (fun ω x => t • A ω x) ht
    (fun ω (σ : Fin (r + 1) → X) => Y ω (σ 0) * D ω σ) hYDm (mul_nonneg hK hc)
    (fun ω σ => by rw [abs_mul]; exact mul_le_mul (hYb ω _) (hD ω σ) (abs_nonneg _) hK)
  have hiV := integrable_randomCoefficient_mean (P := P) hν (fun ω x => t • A ω x) ht D hDm hc hD
  simp only [cylinderField_smul] at hiU hiV
  refine ⟨hEi, ?_⟩
  exact random_replica_energy_covariance_bound (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (H := fun p => t * cylinderField (A p.1.1 p.2) p.1.2) (Y := fun p => Y p.1.1 p.2)
    (fun p => D p.1.1 p.2)
    (hDm.comp (measurable_fst.fst.prodMk measurable_snd)) hc (fun z => hD z.1) b
    (he.mono fun _ hz => hz t) hYi hiU hiV hEi

/-- No constant self-overlap is imposed at finite N. Its actual Gibbs L1
fluctuation controls precisely the extra covariance in the GG estimate. -/
theorem randomCoefficient_diagonal_covariance_le (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hcross : Measurable (fun p : Ω × (X × X) => cylinderCross (A p.1 p.2.1) (A p.1 p.2.2)))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t d : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) :
    |randomCoefficientAverage P ν A t
        (fun ω σ => D ω σ * cylinderCross (A ω (σ 0)) (A ω (σ 0))) -
      randomCoefficientAverage P ν A t D * randomCoefficientAverage P ν A t
        (fun ω (σ : Fin 1 → X) => cylinderCross (A ω (σ 0)) (A ω (σ 0)))| ≤
    2 * c * (∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderCross (A z.1 x) (A z.1 x) - d|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
        ∂P.prod gaussianCoordinates) := by
  let Y := fun (ω : Ω) (x : X) => cylinderCross (A ω x) (A ω x)
  have hYm : Measurable (Function.uncurry Y) := by
    have hp : Measurable (fun p : Ω × X => (p.1, (p.2, p.2))) :=
      measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)
    exact hcross.comp hp
  have hYb (ω : Ω) (x : X) : |Y ω x| ≤ |B| := cylinderCross_bound (A ω) (hA ω) x x
  let E := ∫ z : Ω × (ℕ → ℝ), ∫ x, |Y z.1 x - d|
    ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
      ∂P.prod gaussianCoordinates
  let V := randomCoefficientAverage P ν A t D
  let L := randomCoefficientAverage P ν A t (fun ω σ => D ω σ * Y ω (σ 0))
  let L₀ := randomCoefficientAverage P ν A t (fun ω (σ : Fin 1 → X) => Y ω (σ 0))
  have hL : |L - d * V| ≤ c * E := by
    have h := (randomCoefficient_bounded_observable_covariance (P := P) hν A hAm hA t d
      Y hYm (abs_nonneg B) hYb D hDm hc hD).2
    have heq : (fun ω σ => Y ω (σ 0) * D ω σ) = (fun ω σ => D ω σ * Y ω (σ 0)) := by
      funext ω σ
      exact mul_comm _ _
    rw [heq] at h
    exact h
  have hL₀ : |L₀ - d| ≤ E := by
    have h := (randomCoefficient_bounded_observable_covariance (P := P) (r := 0)
      hν A hAm hA t d Y hYm (abs_nonneg B) hYb
      (fun (_ : Ω) (_ : Fin 1 → X) => 1) measurable_const (c := 1) (by norm_num)
      (fun _ _ => by norm_num)).2
    simpa only [mul_one, randomCoefficientAverage_one hν A hAm hA, one_mul] using h
  have hV : |V| ≤ c := randomCoefficientAverage_abs_le hν A hAm t D hDm hc hD
  change |L - V * L₀| ≤ 2 * c * E
  calc
    _ = |(L - d * V) - V * (L₀ - d)| := by congr 1; ring
    _ ≤ |L - d * V| + |V| * |L₀ - d| := by
      simpa only [abs_mul] using (abs_sub (L - d * V) (V * (L₀ - d)))
    _ ≤ c * E + c * E := add_le_add hL (mul_le_mul hV hL₀ (abs_nonneg _) hc)
    _ = _ := by ring

/-- Quantitative GG with both errors expressed as actual Gibbs L1 deviations.
The energy fluctuation is divided by the perturbation scale when passing to
the limiting GG identities; the diagonal fluctuation is not. -/
theorem randomCoefficient_gaussian_gg_L1_bound (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hcross : Measurable (fun p : Ω × (X × X) => cylinderCross (A p.1 p.2.1) (A p.1 p.2.2)))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    (t b d : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
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
    2 * c * ((∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A z.1 x) z.2 - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
        ∂P.prod gaussianCoordinates) +
      |t| * (∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderCross (A z.1 x) (A z.1 x) - d|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
          ∂P.prod gaussianCoordinates)) := by
  have hg := randomCoefficient_gaussian_gg_bound (P := P) hν A hAm hcross hA t b D hDm hc hD hE
  have hd := randomCoefficient_diagonal_covariance_le (P := P) hν A hAm hcross hA t d D hDm hc hD
  refine hg.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (abs_nonneg t))).trans_eq ?_)
  ring

end InvariantIsing

end

end OAI
