import OAI.Analysis.KadisonKastler.GraphIsometryTransport
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # Algebraic vectors under the graph isometry and its adjoint -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H →ₗᵢ[ℂ] K) (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K)
  (Ω : H) (ξ : K) (c : ℝ) (a : H →L[ℂ] H) (b : K →L[ℂ] K)

theorem graphIsometry_vector
    (h0 : V (a Ω) = b ξ) (h1 : V (star a Ω) = star b ξ) :
    graphIsometry V J L (rescaledGraphVector J Ω c a) = rescaledGraphVector L ξ c b := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · change L (V (J.symm (c • J (star a Ω)))) = c • L (star b ξ)
    simp only [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal,
      J.symm_apply_apply, RingHom.id_apply, h1]

theorem graphIsometry_adjoint_vector
    (h0 : V.toContinuousLinearMap.adjoint (b ξ) = a Ω)
    (h1 : V.toContinuousLinearMap.adjoint (star b ξ) = star a Ω) :
    (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ c b) =
      rescaledGraphVector J Ω c a := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  change inner ℂ (V (v 0)) (b ξ) +
      inner ℂ (L (V (J.symm (v 1)))) (c • L (star b ξ)) =
    inner ℂ (v 0) (a Ω) + inner ℂ (v 1) (c • J (star a Ω))
  simp only [← Complex.coe_smul, inner_smul_right]
  have hv (y : H) (z : K) : inner ℂ (V y) z =
      inner ℂ y (V.toContinuousLinearMap.adjoint z) :=
    (ContinuousLinearMap.adjoint_inner_right V.toContinuousLinearMap y z).symm
  rw [hv, h0, conjugateIsometry_inner, hv, h1]
  have hj := conjugateIsometry_inner J (J.symm (v 1)) (star a Ω)
  rw [J.apply_symm_apply] at hj
  rw [← hj]

end

end KadisonKastler

end OAI
