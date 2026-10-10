import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCompressionGeometry

namespace OAI

/-! The creation and zero-block consequences of the reduced-word action.
Only its action on elementary words is needed; the operator block bounds are
derived by the isometric word coordinates and density. -/

noncomputable section
namespace KadisonSimilarity

variable {E K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Insert the centered first letter and then use the reduced-word inclusion. -/
def reducedCreator (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) : K →L[ℂ] H :=
  C.toContinuousLinearMap.comp (hilbertTensorInsert b)

omit [CompleteSpace K] [CompleteSpace H] in
@[simp] theorem reducedCreator_apply (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) (x : K) :
    reducedCreator C b x = C (hilbertTensorInsert b x) := rfl

omit [CompleteSpace K] [CompleteSpace H] in
theorem norm_reducedCreator_le (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) :
    ‖reducedCreator C b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖C (hilbertTensorInsert b x)‖ ≤ ‖b‖ * ‖x‖
  rw [LinearIsometry.norm_map, norm_hilbertTensorInsert]

/-- The reduced-word formula on words not beginning in the chosen free factor
implies both the vanishing diagonal block and the L² creation bound. -/
theorem reduced_word_creation_blocks
    (J : K →ₗᵢ[ℂ] H) (C : HilbertTensor E K →ₗᵢ[ℂ] H)
    (P T : H →L[ℂ] H) (b : E)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint = 1 - P)
    (hcreator : ∀ x, P (C (hilbertTensorInsert b x)) = C (hilbertTensorInsert b x))
    (hword : ∀ x, T (J x) = C (hilbertTensorInsert b x)) :
    (1 - P) * T * (1 - P) = 0 ∧ ‖P * T * (1 - P)‖ ≤ ‖b‖ := by
  let J₀ := J.toContinuousLinearMap
  have hQ (x : H) : (1 - P) x = J (J₀.adjoint x) := by
    exact congrArg (fun B : H →L[ℂ] H => B x) hcomplement.symm
  have hzero : (1 - P) * T * (1 - P) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change (1 - P) (T ((1 - P) x)) = 0
    rw [hQ x, hword]
    change C (hilbertTensorInsert b (J₀.adjoint x)) -
      P (C (hilbertTensorInsert b (J₀.adjoint x))) = 0
    rw [hcreator, sub_self]
  have hblock : P * T * (1 - P) = (reducedCreator C b).comp J₀.adjoint := by
    apply ContinuousLinearMap.ext
    intro x
    change P (T ((1 - P) x)) = _
    rw [hQ, hword, hcreator]
    rfl
  refine ⟨hzero, ?_⟩
  rw [hblock]
  calc
    _ ≤ ‖reducedCreator C b‖ * ‖J₀.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖b‖ * 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul (norm_reducedCreator_le C b) J.norm_toContinuousLinearMap_le
        (norm_nonneg _) (norm_nonneg _)
    _ = ‖b‖ := mul_one _

/-- The elementary reduced-word action is sufficient for the narrow-arc
compression estimate. The creation bound and zero block are conclusions. -/
theorem norm_narrow_arc_of_reduced_word_action
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : K →L[ℂ] K)
    (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e T : HilbertTensor E K →L[ℂ] HilbertTensor E K)
    (he : e.adjoint = e) (hesq : e * e = e) (hT : T.adjoint = T)
    (heword : ∀ x, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (J : L →ₗᵢ[ℂ] HilbertTensor E K) (C : HilbertTensor B L →ₗᵢ[ℂ] HilbertTensor E K)
    (b : B)
    (hcomplement : J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint =
      1 - firstLetterProjection Ω Q)
    (hcreator : ∀ x, firstLetterProjection Ω Q (C (hilbertTensorInsert b x)) =
      C (hilbertTensorInsert b x))
    (hword : ∀ x, T (J x) = C (hilbertTensorInsert b x))
    {u : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u)
    (h₂ : ‖b‖ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) :
    ‖e * T * e‖ ≤ 3 * u := by
  obtain ⟨hzero, hcreate⟩ := reduced_word_creation_blocks J C
    (firstLetterProjection Ω Q) T b hcomplement hcreator hword
  exact norm_narrow_arc_from_tensor_geometry Ω eΩ hΩ Q hQ hQsq hQnorm e T he hesq hT
    heword hu hsq (norm_nonneg b) hzero hcreate h₂ hnorm

end KadisonSimilarity

end

end OAI
