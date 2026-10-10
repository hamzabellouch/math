import Mathlib

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
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology
open Set unitInterval

namespace CannonVariation

open Set

lemma ordered_variation_path {X : Type*} [TopologicalSpace X]
    (Ω : Set X) (hΩ : IsPathConnected Ω) (W : X → ℝ)
    (hvar : ∃ v ∈ Ω, ∃ w ∈ Ω, W v ≠ W w) :
    ∃ v w : X, ∃ q : Path v w, range q ⊆ Ω ∧ W v < W w := by
  obtain ⟨v,hv,w,hw,hvw⟩ := hvar
  have hj := hΩ.joinedIn v hv w hw
  rcases lt_or_gt_of_ne hvw with hlt | hgt
  · exact ⟨v,w,hj.somePath,by rintro x ⟨t,rfl⟩; exact hj.somePath_mem t,hlt⟩
  · exact ⟨w,v,hj.symm.somePath,by rintro x ⟨t,rfl⟩; exact hj.symm.somePath_mem t,hgt⟩

end CannonVariation

end
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
