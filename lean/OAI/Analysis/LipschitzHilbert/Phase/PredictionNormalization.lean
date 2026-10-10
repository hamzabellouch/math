import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# From probability averages to normalized prediction steps

The probability-mixture transfer, step supremum control, and normalization
costs used in §9. All averages below are actual Bochner integrals.
-/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α : Type*} [MeasurableSpace α]

/-- Transfer from the band-limited mixture to its principal probability.
The loss is proportional to the lower deviation of the prediction. -/
theorem probability_mixture_average_le (ω τ : Measure α)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ] (B : α → ℝ)
    {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hω : Integrable B ω) (hτ : Integrable B τ)
    (hlower : ∀ᵐ x ∂τ, 1 - ε ≤ B x)
    (haverage : (∫ x, B x ∂(ENNReal.ofReal (1 - η) • ω + ENNReal.ofReal η • τ)) ≤ 1) :
    (∫ x, B x ∂ω) ≤ 1 + η / (1 - η) * ε := by
  have hη : 0 < 1 - η := sub_pos.mpr hη1
  have hl : 1 - ε ≤ ∫ x, B x ∂τ := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae (integrable_const (1 - ε)) hτ hlower
  rw [integral_add_measure (hω.smul_measure ENNReal.ofReal_ne_top)
    (hτ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hη.le, ENNReal.toReal_ofReal hη0, smul_eq_mul, smul_eq_mul] at haverage
  apply (mul_le_mul_iff_right₀ hη).mp
  have hmul := mul_le_mul_of_nonneg_left hl hη0
  have heq : (1 - η) * (1 + η / (1 - η) * ε) = 1 - η * (1 - ε) := by
    field_simp
    ring
  rw [heq]
  nlinarith

/-- Blending with the constant one preserves an upper average and shrinks
pointwise lower deviations by the exact blend factor. -/
theorem blend_average_and_lower (ν : Measure α) [IsProbabilityMeasure ν]
    (B : α → ℝ) {θ ε : ℝ} (hθ1 : θ ≤ 1)
    (hB : Integrable B ν) (haverage : ∫ x, B x ∂ν ≤ 1)
    (hlower : ∀ x, 1 - ε ≤ B x) :
    (∫ x, ((1 - θ) * B x + θ) ∂ν) ≤ 1 ∧
      ∀ x, 1 - (1 - θ) * ε ≤ (1 - θ) * B x + θ := by
  constructor
  · rw [integral_add (hB.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left haverage (sub_nonneg.mpr hθ1)]
  · intro x
    nlinarith [mul_le_mul_of_nonneg_left (hlower x) (sub_nonneg.mpr hθ1)]

/-- Supremum on one step cell. -/
def predictionCellSup (B : α → ℝ) (I : Set α) : ℝ := sSup (B '' I)

omit [MeasurableSpace α] in
/-- A log-oscillation bound gives the precise multiplicative cell-supremum
bound. It also proves the relevant supremum is finite. -/
theorem prediction_cell_sup_bounds (B : α → ℝ) (I : Set α) {x : α} (hx : x ∈ I)
    (hpositive : ∀ y ∈ I, 0 < B y) {c : ℝ}
    (hosc : ∀ y ∈ I, |Real.log (B y) - Real.log (B x)| ≤ c) :
    B x ≤ predictionCellSup B I ∧ predictionCellSup B I ≤ Real.exp c * B x := by
  have hupper (y : α) (hy : y ∈ I) : B y ≤ Real.exp c * B x := by
    calc
      B y = Real.exp (Real.log (B y)) := (Real.exp_log (hpositive y hy)).symm
      _ ≤ Real.exp (c + Real.log (B x)) := Real.exp_le_exp.mpr (by
        have h := (abs_le.mp (hosc y hy)).2
        linarith)
      _ = Real.exp c * B x := by rw [Real.exp_add, Real.exp_log (hpositive x hx)]
  have hbounded : BddAbove (B '' I) := ⟨Real.exp c * B x, by
    rintro z ⟨y, hy, rfl⟩
    exact hupper y hy⟩
  exact ⟨le_csSup hbounded ⟨x, hx, rfl⟩,
    csSup_le ⟨B x, x, hx, rfl⟩ (by rintro z ⟨y, hy, rfl⟩; exact hupper y hy)⟩

/-- The normalization denominator from §9. -/
def predictionNormalizer (ν : Measure α) (Bsharp : α → ℝ) : ℝ :=
  max 1 (∫ x, Bsharp x ∂ν)

/-- The normalized step prediction. -/
def normalizedPrediction (ν : Measure α) (Bsharp : α → ℝ) (x : α) : ℝ :=
  Bsharp x / predictionNormalizer ν Bsharp

theorem predictionNormalizer_pos (ν : Measure α) (Bsharp : α → ℝ) :
    0 < predictionNormalizer ν Bsharp :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem normalizedPrediction_nonnegative (ν : Measure α) (Bsharp : α → ℝ)
    (hB : ∀ x, 0 ≤ Bsharp x) (x : α) : 0 ≤ normalizedPrediction ν Bsharp x :=
  div_nonneg (hB x) (predictionNormalizer_pos ν Bsharp).le

theorem normalizedPrediction_average_le_one (ν : Measure α) (Bsharp : α → ℝ) :
    (∫ x, normalizedPrediction ν Bsharp x ∂ν) ≤ 1 := by
  simp only [normalizedPrediction, integral_div]
  exact (div_le_one (predictionNormalizer_pos ν Bsharp)).2 (le_max_right _ _)

theorem predictionNormalizer_log_le (ν : Measure α) (Bsharp : α → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (haverage : ∫ x, Bsharp x ∂ν ≤ Real.exp c) :
    Real.log (predictionNormalizer ν Bsharp) ≤ c := by
  apply (Real.log_le_iff_le_exp (predictionNormalizer_pos ν Bsharp)).2
  exact max_le (Real.one_le_exp hc) haverage

/-- Exponential step oscillation and an additive average error yield an
additive logarithmic normalization cost. -/
theorem step_normalization_cost (ν : Measure α)
    (B Bsharp : α → ℝ) {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hB : Integrable B ν) (hsharp : Integrable Bsharp ν)
    (hmajorant : ∀ᵐ x ∂ν, Bsharp x ≤ Real.exp (b * u) * B x)
    (haverage : ∫ x, B x ∂ν ≤ 1 + a * u) :
    Real.log (predictionNormalizer ν Bsharp) ≤ (a + b) * u := by
  apply predictionNormalizer_log_le ν Bsharp (mul_nonneg (add_nonneg ha hb) hu)
  have hi := integral_mono_ae hsharp (hB.const_mul (Real.exp (b * u))) hmajorant
  rw [integral_const_mul] at hi
  calc
    _ ≤ Real.exp (b * u) * (1 + a * u) :=
      hi.trans (mul_le_mul_of_nonneg_left haverage (Real.exp_pos _).le)
    _ ≤ Real.exp (b * u) * Real.exp (a * u) :=
      mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (a * u))
        (Real.exp_pos _).le
    _ = Real.exp ((a + b) * u) := by rw [← Real.exp_add]; congr 1; ring

/-- The pointwise comparison survives step majorization and normalization,
with the logarithmic normalization cost added to its exponent. -/
theorem prediction_domination_after_normalization (ν : Measure α)
    (B Bsharp β : α → ℝ) {a c u : ℝ}
    (hsharp : ∀ x, B x ≤ Bsharp x) (hsharp0 : ∀ x, 0 ≤ Bsharp x)
    (hcomparison : ∀ x, β x ≤ Real.exp (a * u) * B x)
    (hcost : Real.log (predictionNormalizer ν Bsharp) ≤ c * u) (x : α) :
    β x ≤ Real.exp ((a + c) * u) * normalizedPrediction ν Bsharp x := by
  have hm : 0 < predictionNormalizer ν Bsharp := predictionNormalizer_pos ν Bsharp
  have hmexp : predictionNormalizer ν Bsharp ≤ Real.exp (c * u) :=
    (Real.log_le_iff_le_exp hm).mp hcost
  have hΓ : 0 ≤ normalizedPrediction ν Bsharp x :=
    normalizedPrediction_nonnegative ν Bsharp hsharp0 x
  have hrestore : Bsharp x = predictionNormalizer ν Bsharp * normalizedPrediction ν Bsharp x := by
    unfold normalizedPrediction
    field_simp
  calc
    β x ≤ Real.exp (a * u) * B x := hcomparison x
    _ ≤ Real.exp (a * u) * Bsharp x :=
      mul_le_mul_of_nonneg_left (hsharp x) (Real.exp_pos _).le
    _ = (Real.exp (a * u) * predictionNormalizer ν Bsharp) *
        normalizedPrediction ν Bsharp x := by rw [hrestore]; ring
    _ ≤ (Real.exp (a * u) * Real.exp (c * u)) * normalizedPrediction ν Bsharp x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmexp (Real.exp_pos _).le) hΓ
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end LipschitzHilbert

end

end OAI
