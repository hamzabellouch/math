import Mathlib
import OAI.Geometry.Cannon.Flows.Oscillation

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open Set Filter Topology TopologicalSpace Metric

namespace CannonCrossEnergy

lemma oscillation_mono_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {S : Set X} {T : Set Y}
    (hS : S.Nonempty) (hT₁ : BddAbove (g '' T)) (hT₂ : BddBelow (g '' T))
    (hsub : f '' S ⊆ g '' T) :
    0 ≤ oscillation f S ∧ oscillation f S ≤ oscillation g T := by
  have hne := hS.image f
  exact ⟨sub_nonneg.mpr (csInf_le_csSup hne (hT₂.mono hsub) (hT₁.mono hsub)),
    sub_le_sub (csSup_le_csSup hT₁ hne hsub) (csInf_le_csInf hT₂ hne hsub)⟩

end CannonCrossEnergy

end
end
end
end
end
end
end
end
end

end OAI
