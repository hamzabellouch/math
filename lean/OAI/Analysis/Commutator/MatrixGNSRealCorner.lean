import Mathlib
import OAI.Analysis.Commutator.MatrixGNSCornerBound

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison

lemma positive_re_le_nat_inv {z : ℂ} (hz : 0≤z) (n : ℕ)
    (h : z.re≤(n:ℝ)⁻¹) : z≤(n:ℂ)⁻¹ := by
  rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,←Complex.ofReal_inv]
  exact ⟨h,hz.2.symm⟩

namespace OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance : DecidableEq ι := Classical.decEq ι

variable (τ : M →ₚ[ℂ] ℂ)

theorem matrixGNSOperator_small_real_corner (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0≤c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖≤c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : (MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)).re≤(Fintype.card ι : ℝ)⁻¹)
    (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖≤c*‖X‖ := by
  apply matrixGNSOperator_small_corner ι i₀ M Q hQM τ hQ hτ hfaith h1 T hTQ hc hbound f hf _ X hX
  exact positive_re_le_nat_inv
    ((MatrixGNS.trace (ι:=ι) τ).map_nonneg ((hf.map (matrixInclusion ι i₀ M Q hQM)).nonneg))
    (Fintype.card ι) htrace

end OperatorAmplification

end Kadison

end

end
end

end OAI
