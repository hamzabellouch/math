import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Problem367.StoppedTimePrimitive

def stopDensity {Ω : Type*} (a : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ τ ω then a t ω else 0

theorem integral_indicator_min (a : ℝ → ℝ) (t u : ℝ≥0) :
    (∫ r in (0 : ℝ)..(t : ℝ), if r ≤ u then a r else 0) =
      ∫ r in (0 : ℝ)..(min t u : ℝ≥0), a r := by
  rcases le_total t u with h | h
  · rw [min_eq_left h]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le t.coe_nonneg] at hr
    exact ite_eq_left (hr.2.trans h)
  · rw [min_eq_right h]
    exact intervalIntegral.integral_indicator ⟨u.coe_nonneg, h⟩

theorem stoppedProcess_primitive {Ω : Type*} (a : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (nnrealTimePrimitive a) τ t ω =
      nnrealTimePrimitive (stopDensity a τ) t ω := by
  cases hτ : τ ω with
  | top => simp only [stoppedProcess, nnrealTimePrimitive, stopDensity, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top, ite_true]
  | coe u =>
    simp only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, nnrealTimePrimitive, stopDensity, WithTop.coe_le_coe,
      Real.toNNReal_le_iff_le_coe]
    exact (integral_indicator_min (fun r => a r.toNNReal ω) t u).symm

theorem continuous_stoppedProcess {Ω E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} {ω : Ω} (hX : Continuous (fun t => X t ω))
    (τ : Ω → WithTop ℝ≥0) : Continuous (fun t => stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [stoppedProcess, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe] using hX
  | coe u =>
    simpa only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using hX.comp (continuous_id.min continuous_const)

theorem monotone_stoppedProcess {Ω E : Type*} [Preorder E]
    {X : ℝ≥0 → Ω → E} {ω : Ω} (hX : Monotone (fun t => X t ω))
    (τ : Ω → WithTop ℝ≥0) : Monotone (fun t => stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [stoppedProcess, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe] using hX
  | coe u =>
    simpa only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using hX.comp (monotone_id.min monotone_const)

theorem stopTime_eq_iff_le {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (min (t : WithTop ℝ≥0) (τ ω)).untopA = t ↔ (t : WithTop ℝ≥0) ≤ τ ω := by
  cases hτ : τ ω with
  | top => simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top]
  | coe u => simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, min_eq_left_iff, WithTop.coe_le_coe]

theorem isStronglyProgressive_stopDensity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (ha : IsStronglyProgressive F a) (hτ : IsStoppingTime F τ) :
    IsStronglyProgressive F (stopDensity a τ) := by
  intro T
  let : MeasurableSpace Ω := F T
  have hs : MeasurableSet {p : Iic T × Ω | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2} := by
    simp only [← stopTime_eq_iff_le]
    exact measurableSet_eq_fun (isStronglyProgressive_min_stopping_time hτ T).measurable
      measurable_fst.subtype_val
  exact (ha T).piecewise hs stronglyMeasurable_const

theorem stoppedProcess_weighted_primitive {Ω E : Type*}
    (X : ℝ≥0 → Ω → E) (f : E → ℝ) (a : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (nnrealTimePrimitive (fun s ω => f (X s ω) * a s ω)) τ t ω =
      nnrealTimePrimitive (fun s ω => f (stoppedProcess X τ s ω) * stopDensity a τ s ω) t ω := by
  rw [stoppedProcess_primitive]
  congr 1
  funext s ω
  by_cases h : (s : WithTop ℝ≥0) ≤ τ ω
  · simp only [stopDensity, h, ite_true, stoppedProcess_eq_of_le h]
  · simp only [stopDensity, h, ite_false, mul_zero]

end Problem367.StoppedTimePrimitive

end

end OAI
