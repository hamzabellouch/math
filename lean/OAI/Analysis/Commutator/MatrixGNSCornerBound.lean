import Mathlib
import OAI.Analysis.Commutator.FiniteMatrixSmallCorner
import OAI.Analysis.Commutator.MatrixGNSUnitary
import OAI.Analysis.Commutator.UnitaryCommuteNorm

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance : DecidableEq ι := Classical.decEq ι

variable (τ : M →ₚ[ℂ] ℂ)

def matrixGNSOperator (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι) :
    (MatrixGNS.trace (ι:=ι) τ).GNS →L[ℂ] (MatrixGNS.trace (ι:=ι) τ).GNS :=
  (MatrixGNS.unitary (ι:=ι) τ).symm.conjStarAlgEquiv
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T)

lemma matrixGNSOperator_commutator_norm
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : CStarMatrix ι ι M) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖=
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ X-
      MatrixGNS.representation τ X*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖ := by
  exact UnitaryTransport.commutator_norm_of_conjugates (MatrixGNS.unitary (ι:=ι) τ)
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T) (MatrixGNS.representation τ X)
    ((MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X) (MatrixGNS.unitary_conjugates τ X)

lemma matrixGNSOperator_commutes
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hT : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    (X : matrixVonNeumann ι i₀ Q) :
    matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X)=
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X)*matrixGNSOperator ι M τ T := by
  apply UnitaryTransport.commutes_of_conjugates (MatrixGNS.unitary (ι:=ι) τ)
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T)
    (MatrixGNS.representation τ (matrixInclusion ι i₀ M Q hQM X))
    ((MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X))
    (MatrixGNS.unitary_conjugates τ (matrixInclusion ι i₀ M Q hQM X))
  exact matrixInclusion_commutes ι i₀ M Q hQM
    ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) T hT X

theorem matrixGNSOperator_small_corner (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0≤c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖≤c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)≤(Fintype.card ι : ℂ)⁻¹)
    (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖≤c*‖X‖ := by
  apply (matrixGNSOperator_commutator_norm ι M τ T X).le.trans
  rw [matrixTrace_restrict] at htrace
  exact matrix_small_corner_bound ι i₀ M Q hQM hQ (NormalSubalgebra.trace M Q hQM τ)
    (NormalSubalgebra.tracial M Q hQM τ hτ) (NormalSubalgebra.faithful M Q hQM τ hfaith)
    (NormalSubalgebra.one M Q hQM τ h1) ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom)
    T hTQ hc hbound f hf htrace X hX

end Kadison.OperatorAmplification

end

end
end

end OAI
