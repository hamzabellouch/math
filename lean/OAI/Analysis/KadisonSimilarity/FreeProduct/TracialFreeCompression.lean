import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseCommutatorCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseSymmetry
import OAI.Analysis.KadisonSimilarity.Representation.ReducedCreationBlocks
import OAI.Analysis.KadisonSimilarity.Tensor.TensorHeadSlices

namespace OAI

/-! The free-compression norm bound in the faithful tracial representation.
The hypotheses describe only the elementary reduced-word coordinates; their
zero block, creation bound, and the small-corner norm bound are conclusions. -/

noncomputable section
namespace KadisonSimilarity

variable {P H F K : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A Z : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (Z : Set P)]

omit [IsClosed (A : Set P)] in
/-- The faithful tracial norm and the elementary creation action give the
order-`u` bound used for the narrow spectral arc. -/
theorem norm_narrow_compression_of_reduced_words
    (hfaithful : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (W : H ≃ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) F)
    (hhead : ∀ (a : A) x, W (G.left (a : P) x) =
      tensorHeadAction (G.baseRepresentation A a) (W x))
    (Q : F →L[ℂ] F) (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (J : K →ₗᵢ[ℂ] HilbertTensor (G.baseSpace A) F)
    (C : HilbertTensor (centeredSubspace (G.baseVector Z 1)) K →ₗᵢ[ℂ]
      HilbertTensor (G.baseSpace A) F)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint =
      1 - firstLetterProjection (G.baseVector A 1) Q)
    (e : A) (he : IsStarProjection (e : P))
    (b : Z) (hbself : star b = b) (hb0 : G.trace (b : P) = 0)
    (hcreator : ∀ x, firstLetterProjection (G.baseVector A 1) Q
      (C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x)) =
        C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x))
    (hword : ∀ x, W (G.left (b : P) (W.symm (J x))) =
      C (hilbertTensorInsert (G.baseSymmetryLetter Z b hb0) x))
    {u : ℝ} (hu : 0 ≤ u) (hetrace : G.trace (e : P) = (u : ℂ))
    (hb₂ : (G.trace (star (b : P) * (b : P))).re ≤ u) (hbnorm : ‖(b : P)‖ ≤ 1) :
    ‖(e : P) * (b : P) * (e : P)‖ ≤ 3 * u := by
  let ρ := W.conjStarAlgEquiv.toStarAlgHom.comp G.left
  have hρinjective : Function.Injective ρ := by
    intro a b hab
    apply G.left_injective hfaithful
    apply W.conjStarAlgEquiv.injective
    exact hab
  have hρnorm (x : P) : ‖ρ x‖ = ‖x‖ := by
    exact NonUnitalStarAlgHom.norm_map ρ hρinjective x
  have hΩ : ‖G.baseVector A 1‖ = 1 := by
    have hsq : ‖G.baseVector A 1‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
      change (G.trace (star (1 : P) * 1)).re = 1
      simp only [star_one, one_mul, hτ, Complex.one_re]
    nlinarith [norm_nonneg (G.baseVector A 1)]
  have heΩ : ‖G.baseVector A e‖ ^ 2 = u := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner,
      he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, hetrace]
    rfl
  have heword (x : F) : ρ (e : P) (hilbertTensorInsert (G.baseVector A 1) x) =
      hilbertTensorInsert (G.baseVector A e) x := by
    change W (G.left (e : P) (W.symm _)) = _
    rw [hhead, W.apply_symm_apply, tensorHeadAction_insert]
    have hv : G.baseRepresentation A e (G.baseVector A 1) = G.baseVector A e := by
      apply Subtype.ext
      change G.left (e : P) (G.vector 1) = G.vector (e : P)
      rw [G.left_vector, mul_one]
    rw [hv]
  have hestar : (ρ (e : P)).adjoint = ρ (e : P) := by
    change star (ρ (e : P)) = ρ (e : P)
    exact (map_star ρ (e : P)).symm.trans (congrArg ρ he.isSelfAdjoint.star_eq)
  have hesq : ρ (e : P) * ρ (e : P) = ρ (e : P) := by
    rw [← map_mul, he.isIdempotentElem.eq]
  have hbstar : (ρ (b : P)).adjoint = ρ (b : P) := by
    change star (ρ (b : P)) = ρ (b : P)
    exact (map_star ρ (b : P)).symm.trans
      (congrArg ρ (congrArg (fun z : Z => (z : P)) hbself))
  have hbvec : ‖G.baseSymmetryLetter Z b hb0‖ ^ 2 ≤ u := by
    change ‖G.baseVector Z b‖ ^ 2 ≤ u
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    exact hb₂
  have hbound := norm_narrow_arc_of_reduced_word_action
    (G.baseVector A 1) (G.baseVector A e) hΩ Q hQ hQsq hQnorm
    (ρ (e : P)) (ρ (b : P)) hestar hesq hbstar heword J C
    (G.baseSymmetryLetter Z b hb0) hcomplement hcreator hword hu heΩ hbvec
    (by rw [hρnorm]; exact hbnorm)
  rw [← map_mul, ← map_mul, hρnorm] at hbound
  exact hbound

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
