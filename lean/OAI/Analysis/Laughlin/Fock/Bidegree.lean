import OAI.Analysis.Laughlin.Fock.Inner

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_empty (Q : ℕ) : occupationBasis Q ∅ = (1 : Space Q) := by
  let A : Set.powersetCard (Fin (Q+1)) 0 := ⟨∅,rfl⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_zero_apply]

def OccupationBidegree (Q n w : ℕ) (x : Space Q) : Prop :=
  ∀ A : Finset (Fin (Q+1)), (A.card ≠ n ∨ (∑ i ∈ A, i.val) ≠ w) →
    (occupationBasis Q).repr x A = 0

theorem vacuum_bidegree (Q : ℕ) : OccupationBidegree Q 0 0 (1 : Space Q) := by
  intro A hA
  have hn : (∅ : Finset (Fin (Q+1))) ≠ A := by intro he; subst A; simp at hA
  rw [← occupation_empty]
  simp [Module.Basis.repr_self,hn]

theorem create_bidegree (Q n w : ℕ) (x : Space Q) (hx : OccupationBidegree Q n w x)
    (i : Fin (Q+1)) : OccupationBidegree Q (n+1) (w+i.val) (create i x) := by
  intro A hA
  rw [create_coordinate]
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi]
    have hc := Finset.card_erase_of_mem hi
    have hw := Finset.sum_erase_add A (fun j : Fin (Q+1) => j.val) hi
    have hlow : (A.erase i).card ≠ n ∨ (∑ j ∈ A.erase i, j.val) ≠ w := by
      rcases hA with hA | hA
      · left; have hp := Finset.card_pos.mpr ⟨i,hi⟩; omega
      · right; omega
    rw [hx (A.erase i) hlow,mul_zero]
  · rw [ite_eq_right hi]

theorem four_create_bidegree (Q : ℕ) (a b c d : Fin (Q+1)) :
    OccupationBidegree Q 4 (a.val+b.val+c.val+d.val)
      (create a (create b (create c (create d (1 : Space Q))))) := by
  have h := create_bidegree Q _ _ _
    (create_bidegree Q _ _ _ (create_bidegree Q _ _ _
      (create_bidegree Q 0 0 _ (vacuum_bidegree Q) d) c) b) a
  convert h using 1; omega

end Laughlin.Fock

end OAI
