import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace MaxCutGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The range identification induced by a common kernel. -/
def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

/-- This identification respects every original vector, including vectors in
the kernel and maps of rank zero. -/
theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

/-- Finite-dimensional image suffices: the ambient codomain and domain may
otherwise be infinite-dimensional. -/
theorem exists_postcomp_equiv_of_ker_eq (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] (hker : S.ker = T.ker) :
    ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (rangeEquivOfKerEq S T hker)
  refine ⟨g, ?_⟩
  ext x
  change g (S x) = T x
  exact (hg ⟨S x, ⟨x, rfl⟩⟩).symm.trans (rangeEquivOfKerEq_apply S T hker x)

/-- Invertible postcomposition never changes the kernel. Thus the kernel is
an exact orbit invariant, rather than only a necessary condition. -/
theorem ker_eq_iff_exists_postcomp_equiv (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] :
    S.ker = T.ker ↔ ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  constructor
  · exact exists_postcomp_equiv_of_ker_eq S T
  · rintro ⟨g, rfl⟩
    ext x
    simp

end
end MaxCutGames.Inverse.KMSKernelOrbits

end OAI
