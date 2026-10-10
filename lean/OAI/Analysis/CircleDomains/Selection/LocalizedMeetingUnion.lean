import OAI.Analysis.CircleDomains.Selection.CountableMeetingBound
import OAI.Analysis.CircleDomains.Selection.TwoTerminalHitBound

namespace OAI

/-! Splitting a meeting into its physical-domain and dust parts. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem localized_code_meeting_union_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (U B : Set X) (A : Set Y) (π : Y → X)
    (hcover : ∀ x ∈ U, x ∈ B ∨ ∃ y ∈ A, π y = x)
    {b c : ℝ≥0∞}
    (hB : ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ (U ∩ B)).Nonempty} ≤ b)
    (hA : ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ y ∈ A, π y ∈ range p.1.val.1 ∧ π y ∈ range p.2.val.1} ≤ c) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ x ∈ U, x ∈ range p.1.val.1 ∧ x ∈ range p.2.val.1} ≤ b + c := by
  apply (measure_mono (t :=
    {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ (U ∩ B)).Nonempty} ∪
    {p | ∃ y ∈ A, π y ∈ range p.1.val.1 ∧ π y ∈ range p.2.val.1}) ?_).trans
  · exact (measure_union_le _ _).trans (add_le_add hB hA)
  · rintro p ⟨x, hxU, hxp, hxq⟩
    rcases hcover x hxU with hxB | ⟨y, hy, hπy⟩
    · exact Or.inl ⟨x, ⟨hxp, hxq⟩, hxU, hxB⟩
    · exact Or.inr ⟨y, hy, hπy.symm ▸ hxp, hπy.symm ▸ hxq⟩

end CircleDomainRigidity

end

end OAI
