import Mathlib
import OAI.Analysis.Commutator.NormalGNSSeparable
import OAI.Analysis.Commutator.NormalTracedFactorMain

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

theorem separable_traced_factor_bound
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  let := NormalGNS.separable_gns M τ hnormal
  exact traced_factor_bound M τ hτ hnormal hfaith hone hfac hdiffuse h hh Y X hX

end Kadison.NormalRepresentation

end

end
end

end OAI
