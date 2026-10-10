import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GroupDimensionTransport

namespace OAI

/-! # The dimension bound on an increasing supremum of subgroups -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

theorem cohomologicalDimension_le_iSup_of_monotone (K : ℕ → Subgroup G)
    (hK : Monotone K) (d : ℕ)
    (hd : ∀ n, HasProjectiveDimensionLE (trivialIntegral (K n)) d) :
    HasProjectiveDimensionLE (trivialIntegral (⨆ n, K n : Subgroup G)) (d + 1) := by
  let L := ⨆ n, K n
  let S (n : ℕ) : Subgroup L := (K n).subgroupOf L
  have hdir : Directed (· ≤ ·) K :=
    fun n m => ⟨max n m, hK (le_max_left _ _), hK (le_max_right _ _)⟩
  have hS : Monotone S := fun _ _ h => Subgroup.comap_mono (hK h)
  have hcover (g : L) : ∃ n, g ∈ S n :=
    (Subgroup.mem_iSup_of_directed hdir).mp g.property
  apply cohomologicalDimension_le_of_exhaustion S hS hcover d
  intro n
  let := hd n
  exact cohomologicalDimension_le_of_equiv
    (Subgroup.subgroupOfEquivOfLe (le_iSup K n)).symm d

end PolycyclicRecognition

end

end OAI
