import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.FreeAbelianDescent

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

universe u

theorem abelian_descent (A : Type u) [CommGroup A] [Group.FG A] :
    AlgebraicDescent A := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive A)
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let φ := (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  have hs : Surjective φ := by
    intro z
    exact ⟨f.symm (z,0),by simp [φ]⟩
  apply (free_abelian_descent (Fin n →₀ ℤ)).of_finite_kernel φ.toMultiplicativeRight
    (fun z => hs z.toAdd)
  apply ((Set.finite_singleton (0 : Fin n →₀ ℤ)).prod
    (Set.toFinite (Set.univ : Set T))).preimage f.injective.injOn |>.subset
  intro x hx
  exact ⟨hx,Set.mem_univ _⟩

theorem finite_commutator_descent (G : Type u) [Group G] [Group.FG G]
    (hf : (commutator G : Set G).Finite) : AlgebraicDescent G := by
  have hs : Surjective (Abelianization.of : G →* Abelianization G) := QuotientGroup.mk_surjective
  let _ : Group.FG (Abelianization G) := Group.fg_of_surjective hs
  apply (abelian_descent (Abelianization G)).of_finite_kernel Abelianization.of hs
  rwa [Abelianization.ker_of]

end CriticalPercolation
end
end
end

end OAI
