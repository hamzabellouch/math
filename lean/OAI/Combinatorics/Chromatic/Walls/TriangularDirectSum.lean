import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
universe u v w

theorem triangular_directSum_injective {J : Type u} [DecidableEq J] {M : J → Type v} {N : Type w}
    [∀ j,AddCommGroup (M j)] [∀ j,Module ℚ (M j)] [AddCommGroup N] [Module ℚ N]
    (r : J → J → Prop) [IsStrictOrder J r]
    (F : ∀ j,M j →ₗ[ℚ] N) (D : ∀ j,N →ₗ[ℚ] M j)
    (hdiag : ∀ j x,D j (F j x)=x)
    (hoff : ∀ i j,j≠i → ¬r j i → ∀ x,D i (F j x)=0) :
    Function.Injective (DirectSum.toModule ℚ J N F) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hn
  have hs : (x.support : Set J).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h=>hn (DFinsupp.support_eq_empty.mp h))
  have hwf : WellFounded (fun i j=>r i j ∧ i∈x.support ∧ j∈x.support) :=
    Set.wellFoundedOn_iff.mp x.support.finite_toSet.wellFoundedOn
  obtain ⟨i,hi,hm⟩:=hwf.has_min (x.support : Set J) hs
  have H : D i (DirectSum.toModule ℚ J N F x)=x i := by
    calc
      _ = D i (DirectSum.toModule ℚ J N F (∑ j∈x.support,DirectSum.of M j (x j))) :=
        congrArg (fun y=>D i (DirectSum.toModule ℚ J N F y)) (DirectSum.sum_support_of x).symm
      _ = ∑ j∈x.support,D i (F j (x j)) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (D i) (DirectSum.toModule_lof (R:=ℚ) (φ:=F) j (x j))
      _ = x i := by
        rw [Finset.sum_eq_single i]
        · exact hdiag i (x i)
        · intro j hj hji
          exact hoff i j hji (fun h=>hm j hj ⟨h,hj,hi⟩) (x j)
        · intro h; exact (h hi).elim
  rw [hx,map_zero] at H
  exact (DFinsupp.mem_support_iff.mp hi) H.symm
end ElementaryPositivity

end

end OAI
