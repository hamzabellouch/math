import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralFiltrationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MaximalNilpotentNormal

namespace OAI

/-! # Detecting the maximal nilpotent normal subgroup by its central factors -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

def ambientUpperCentralSeries (F : Subgroup G) (n : ℕ) : Subgroup G :=
  (Subgroup.upperCentralSeries F n).map F.subtype

instance ambientUpperCentralSeries_normal (F : Subgroup G) [F.Normal] (n : ℕ) :
    (ambientUpperCentralSeries F n).Normal := by
  dsimp [ambientUpperCentralSeries]
  infer_instance

theorem ambientUpperCentralSeries_mono (F : Subgroup G) :
    Monotone (ambientUpperCentralSeries F) := by
  intro i j hij
  exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono F hij)

theorem ambientUpperCentralSeries_zero (F : Subgroup G) :
    ambientUpperCentralSeries F 0 = ⊥ := by
  simp only [ambientUpperCentralSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem ambientUpperCentralSeries_top (F : Subgroup G) [Group.IsNilpotent F] :
    ambientUpperCentralSeries F (Group.nilpotencyClass F) = F := by
  simp only [ambientUpperCentralSeries, Subgroup.upperCentralSeries_nilpotencyClass,
    Subgroup.map_top, Subgroup.range_subtype]

theorem maximal_nilpotent_normal_of_trivial_central_action [Group.IsSolvable G]
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F)
    (K : Subgroup G) [K.Normal] (hFK : F ≤ K)
    (haction : ∀ i, ⁅K, ambientUpperCentralSeries F (i + 1)⁆ ≤ ambientUpperCentralSeries F i) :
    K = F := by
  have hcentral := centralizer_le_maximal_nilpotent_normal F hmax
  have hK : Group.IsNilpotent K := nilpotent_of_central_filtration_action K
    (ambientUpperCentralSeries F) (ambientUpperCentralSeries_mono F)
    (ambientUpperCentralSeries_zero F) haction (Group.nilpotencyClass F) (by
      rw [ambientUpperCentralSeries_top]
      exact hcentral)
  exact hmax K inferInstance hK hFK

end PolycyclicRecognition

end OAI
