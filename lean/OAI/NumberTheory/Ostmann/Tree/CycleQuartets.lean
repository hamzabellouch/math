import OAI.NumberTheory.Ostmann.Tree.CycleCut
import OAI.NumberTheory.Ostmann.Tree.CycleWalk

namespace OAI

namespace Ostmann.Tree
open scoped BigOperators

def quartetCut (d : ℕ) : Density.Cut (d+2) d := Density.Cut.ofLE (by omega)

theorem exists_quartet_cycle {d b : ℕ} (P : LeafPartition (d+2) b)
    (hb : 4*b ≤ 3*2^(d+2)) :
    Nonempty (BalancedSelection P.label (quartetCut d).label) := by
  apply exists_balanced_selection
  have hr : 2^(d+2)=4*2^d := by rw [pow_add]; ring
  simp only [Leaves,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool]
  omega

theorem quartet_cycle_project {F : Type*} [Field F] {d b : ℕ}
    (P : LeafPartition (d+2) b)
    (c : BalancedSelection P.label (quartetCut d).label)
    (z : Fˣ) (M : Leaves (d+2) → Fˣ) :
    (quartetCut d).project (c.act z M) = (quartetCut d).project M := by
  classical
  funext v
  rw [Density.Cut.project_eq_label_product,Density.Cut.project_eq_label_product]
  exact c.right_product z M v

theorem quartet_cycle_components {F : Type*} [Field F] {d b : ℕ}
    (P : LeafPartition (d+2) b)
    (c : BalancedSelection P.label (quartetCut d).label)
    (z : Fˣ) (M : Leaves (d+2) → Fˣ) :
    P.componentProduct (c.act z M) = P.componentProduct M := by
  classical
  funext v
  exact c.left_product z M v

end Ostmann.Tree

end OAI
