import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Span

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W22

variable {R : Type*} [CommRing R]

noncomputable def cyclicFactorEquiv (I : Ideal R) (f : R) :
    (R ⧸ I.colon {f}) ≃ₗ[R]
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) := by
  let J : Ideal R := I ⊔ Ideal.span {f}
  have hfJ : f ∈ J := (show Ideal.span {f} ≤ J from le_sup_right)
    (Ideal.subset_span (by simp))
  let F : R →ₗ[R] J ⧸ I.submoduleOf J :=
    (I.submoduleOf J).mkQ.comp (LinearMap.toSpanSingleton R J ⟨f, hfJ⟩)
  have hker : LinearMap.ker F = I.colon {f} := by
    ext a
    change ((Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) = 0) ↔
      a ∈ I.colon {f}
    rw [Submodule.Quotient.mk_eq_zero]
    change a * f ∈ I ↔ a ∈ I.colon {f}
    simp only [Submodule.mem_colon_singleton, smul_eq_mul]
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := (I.submoduleOf J).mkQ_surjective y
    have hx : (x : R) ∈ Ideal.span {f} ⊔ I := by
      simpa only [J, sup_comm] using x.property
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hx
    refine ⟨a, ?_⟩
    change (Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) =
      Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    change a * f - (x : R) ∈ I
    rw [← hab]
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using I.neg_mem hb
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)

end WeightedTorusJets.W22


end SiegelZeros

end OAI
