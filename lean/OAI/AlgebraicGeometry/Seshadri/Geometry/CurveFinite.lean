import Mathlib

namespace OAI

section
noncomputable section
                                 
section

namespace MaximalSeshadri.Geometry
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]

lemma proper_irreducible_closed_subsingleton
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hi : IsIrreducible Z) (hp : Z ≠ Set.univ) : Z.Subsingleton := by
  let C : IrreducibleCloseds X := ⟨Z, hi, hZ⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin C := by
    rcases Order.krullDim_le_one_iff.mp hd C with hm | hm
    · exact hm
    · have he : C = T := le_antisymm (Set.subset_univ _) (hm (Set.subset_univ _))
      exact (hp (congrArg SetLike.coe he)).elim
  have hg (x : X) (hx : x ∈ Z) : IsGenericPoint x Z := by
    let D : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : D ≤ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
    have he : D = C := le_antisymm hle (hmin hle)
    exact congrArg SetLike.coe he
  intro x hx y hy
  exact (hg x hx).eq (hg y hy)

theorem proper_closed_finite_of_dimension_one [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hp : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨F, hF, hFc, hFi, hZF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZF]
  apply hF.sUnion
  intro C hC
  apply Set.Subsingleton.finite
  apply proper_irreducible_closed_subsingleton hd (hFc C hC) (hFi C hC)
  intro hc
  apply hp
  apply Set.eq_univ_of_univ_subset
  rw [hZF]
  exact hc ▸ Set.subset_sUnion_of_mem hC

open AlgebraicGeometry in
                                                                            
theorem integral_curve_proper_closed_finite (C : Scheme)
    [IsIntegral C] [IsNoetherian C] (hd : topologicalKrullDim C = 1)
    {Z : Set C} (hZ : IsClosed Z) (hp : Z ≠ Set.univ) : Z.Finite :=
  proper_closed_finite_of_dimension_one hd.le hZ hp

end MaximalSeshadri.Geometry
end


end
end

end OAI
