import Mathlib
import OAI.Computability.MaxCut.Encoding.KMSKernelOrbits
import OAI.Computability.MaxCut.Games.KMSBasisInvariant

namespace OAI

/-! Basis-invariant matrix functions have constant actual Fourier coefficients
on kernel fibers. This uses ambient automorphism transitivity proved from the
first isomorphism theorem, followed by the exact change-of-basis identity for
the normalized trace-character transform. -/

namespace MaxCutGames.Inverse.KMSKernelOrbitsFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant
open MaxCutGames.Inverse.KMSKernelOrbits

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]

/-- Actual coefficients depend on the kernel, not on the chosen embedding of
the quotient into the basis-index space. No coefficient-invariance premise is
assumed beyond the original function's basis invariance. -/
theorem coefficient_eq_of_ker_eq (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (S T : F →ₗ[F2] E) (hker : S.ker = T.ker) :
    linearCoeff f S = linearCoeff f T := by
  obtain ⟨g, hg⟩ := exists_postcomp_equiv_of_ker_eq S T hker
  have h := coefficient_change f hf g S
  rw [hg] at h
  exact h.symm

end
end MaxCutGames.Inverse.KMSKernelOrbitsFourier

end OAI
