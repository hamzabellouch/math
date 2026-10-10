import Mathlib
import OAI.Analysis.Commutator.FiniteSmallCorner
import OAI.Analysis.Commutator.MatrixCommute
import OAI.Analysis.Commutator.MatrixCornerInclusion

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance : DecidableEq ι := Classical.decEq ι

lemma matrixInclusion_commutes (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
      ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
    (X : matrixVonNeumann ι i₀ Q) :
    diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ (matrixInclusion ι i₀ M Q hQM X)=
      CyclicColumns.matrixRepresentation ρ (matrixInclusion ι i₀ M Q hQM X)*diagonal (H:=K) ι T := by
  apply CyclicColumns.diagonal_commutes_matrixRepresentation
  intro i j
  let q : Q := ⟨entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j,
    (mem_matrixVonNeumann ι i₀ Q X).mp X.property i j⟩
  have he : matrixInclusion ι i₀ M Q hQM X i j=NormalSubalgebra.inclusion M Q hQM q := by
    apply Subtype.ext
    exact matrixInclusion_entry ι i₀ M Q hQM X i j
  rw [he]
  exact hT q

theorem matrix_small_corner_bound (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0) (h1 : σ 1=1)
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
      ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
    {c : ℝ} (hc : 0≤c) (hbound : ∀ a : M,‖T*ρ a-ρ a*T‖≤c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : matrixTrace ι i₀ Q σ f≤(Fintype.card ι : ℂ)⁻¹)
    (X : CStarMatrix ι ι M)
    (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ X-
      CyclicColumns.matrixRepresentation ρ X*diagonal (H:=K) ι T‖≤c*‖X‖ := by
  let e : matrixVonNeumann ι i₀ Q := matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i₀ (1:Q))
  have he : IsStarProjection e :=
    (MatrixGNS.rowMatrix_projection (A:=Q) i₀).map (matrixEquiv ι i₀ Q).toStarAlgHom
  have hje : matrixInclusion ι i₀ M Q hQM e=MatrixGNS.rowMatrix i₀ (1:M) :=
    matrixInclusion_row ι i₀ M Q hQM i₀
  have hte : matrixTrace ι i₀ Q σ e=(Fintype.card ι : ℂ)⁻¹ := by
    change matrixTrace ι i₀ Q σ (matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i₀ (1:Q)))=_
    rw [matrixTrace_equiv,MatrixGNS.rowMatrix_trace σ h1]
  refine CornerTransport.finite_small_corner_bound (matrixVonNeumann ι i₀ Q)
    (factor_matrixVonNeumann ι i₀ Q hQ) (matrixTrace ι i₀ Q σ)
    (matrixTrace_tracial ι i₀ Q σ hσ) (matrixTrace_faithful ι i₀ Q σ hfaith)
    (matrixInclusion ι i₀ M Q hQM) (CyclicColumns.matrixRepresentation ρ)
    (diagonal (H:=K) ι T) (matrixInclusion_commutes ι i₀ M Q hQM ρ T hT)
    e he ?_ f hf (by rw [hte]; exact htrace) X hX
  intro Z hZ
  rw [hje] at hZ
  exact MatrixGNS.row_corner_commutator_bound ρ T hc hbound i₀ Z hZ

end Kadison.OperatorAmplification

end

end
end

end OAI
