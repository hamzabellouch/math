import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures

namespace OAI

/-! Each fixed slot distribution is dominated by the mean weighted tuple
measure, and hence inherits its absolute continuity. Inactive slots have
zero mass, so these are subprobability measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def baseCodeSlot (d : PathCodeData X Y) (k : ℕ) (Γ : BasePathCode d) : Measure LevelTuple :=
  slotTupleMeasure (Γ.val.2 k)

theorem measurable_baseCodeSlot (d : PathCodeData X Y) (k : ℕ) :
    Measurable (baseCodeSlot d k) :=
  measurable_slotTupleMeasure.comp
    ((measurable_pi_apply k).comp (measurable_snd.comp measurable_subtype_coe))

def slotLaw (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (k : ℕ) :
    Measure LevelTuple := (P : Measure (BasePathCode d)).bind (baseCodeSlot d k)

theorem slotLaw_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) {A : Set LevelTuple} (hA : MeasurableSet A) :
    slotLaw d P k A = ∫⁻ Γ, slotTupleMeasure (Γ.val.2 k) A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeSlot d k).aemeasurable

theorem slotLaw_univ_le (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) : slotLaw d P k univ ≤ 1 := by
  rw [slotLaw_apply d P k MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ _Γ, (1 : ℝ≥0∞) ∂(P : Measure (BasePathCode d)) :=
      lintegral_mono fun Γ => slotTupleMeasure_univ_le (Γ.val.2 k)
    _ = 1 := by simp

theorem weighted_slotLaw_le (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) : slotWeight k • slotLaw d P k ≤ meanCodeTuple d P := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, slotLaw_apply d P k hA, meanCodeTuple_apply d P hA]
  have hm : Measurable (fun Γ : BasePathCode d => slotTupleMeasure (Γ.val.2 k) A) :=
    (Measure.measurable_coe hA).comp (measurable_baseCodeSlot d k)
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono
  intro Γ
  have h := (Measure.le_iff.mp (weightedTupleMeasure_slot_le Γ.val.2 k)) A hA
  simpa only [Measure.smul_apply, smul_eq_mul] using h

theorem slotLaw_absolutelyContinuous (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (k : ℕ) : slotLaw d P k ≪ τ :=
  (Measure.absolutelyContinuous_smul (slotWeight_pos k).ne').trans
    ((weighted_slotLaw_le d P k).absolutelyContinuous.trans hτ)

end CircleDomainRigidity

end

end OAI
