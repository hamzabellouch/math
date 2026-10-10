import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import OAI.Analysis.CircleDomains.Selection.SquareVisitTolls

namespace OAI

/-! Once diffuse meetings are excluded, independence bounds the remaining
meeting event by the sum of products of the point-hit probabilities. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem code_pair_meeting_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (B D : Set X) (hD : D.Countable)
    (hcontacts : ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range p.1.val.1 ∩ range p.2.val.1 ∩ B ⊆ D) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ B).Nonempty} ≤
        ∑' x : ↥(D ∩ B), codeHitProbability d P x.val * codeHitProbability e Q x.val := by
  let : Countable ↥(D ∩ B) := (hD.mono inter_subset_left).to_subtype
  let A (x : ↥(D ∩ B)) : Set (BasePathCode d × BasePathCode e) :=
    {Γ | x.val ∈ range Γ.val.1} ×ˢ {Δ | x.val ∈ range Δ.val.1}
  have hsub : {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ B).Nonempty} ≤ᵐ[
      (P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))] ⋃ x, A x := by
    filter_upwards [hcontacts] with p hp hmeet
    obtain ⟨x, hx⟩ := hmeet
    exact mem_iUnion.mpr ⟨⟨x, hp hx, hx.2⟩, hx.1⟩
  apply (measure_mono_ae hsub).trans
  apply (measure_iUnion_le A).trans
  apply le_of_eq
  apply tsum_congr
  intro x
  exact Measure.prod_prod _ _

end CircleDomainRigidity

end

end OAI
