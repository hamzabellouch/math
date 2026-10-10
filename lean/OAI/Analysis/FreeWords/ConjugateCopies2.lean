import Mathlib
import OAI.Analysis.FreeWords.ConjugateCopies
import OAI.Analysis.FreeWords.ConjugateFree

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

namespace FreeMatrixCopies

variable (F : FreeMatrixCopies τ r d)

end FreeMatrixCopies

end

end KKFreeWords

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A} {r d : ℕ}

def haarConjugateCopies (hτ : FaithfulTracial τ)
    (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P))
    (I : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A) (hI : Function.Injective I)
    (hIP : I.range ≤ P) (k : Fin r → ℤ) (hk : Function.Injective k) :
    FreeMatrixCopies τ r d where
  inclusion j := (conjugate u (k j)).toStarAlgHom.comp I
  injective j := (conjugate u (k j)).injective.comp hI
  free := by
    have hf := (conjugates_scalarFree hτ.2.1 u hu hHaar hfree).reindex hk
    apply hf.mono
    intro j x hx
    obtain ⟨y,rfl⟩ := hx
    exact StarSubalgebra.mem_map.mpr ⟨I y, hIP ⟨y,rfl⟩, rfl⟩

omit [StarOrderedRing A] in
theorem haarConjugateCopies_diagonal (hτ : FaithfulTracial τ)
    (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P))
    (I : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A) (hI : Function.Injective I)
    (hIP : I.range ≤ P) (k : Fin r → ℤ) (hk : Function.Injective k)
    (j : Fin r) (a : Fin d) :
    (haarConjugateCopies hτ u hu hHaar hfree I hI hIP k hk).diagonal j a =
      upow u (-k j) * I (Matrix.single a a 1) * upow u (k j) := by
  exact conjugate_apply u (k j) _

end

end KKFreeWords
end

end OAI
