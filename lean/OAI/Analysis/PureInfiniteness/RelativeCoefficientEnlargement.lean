import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! The relative-domain coefficient and closure step of KR02 Lemma 7.20.
Domain coefficients lie in the nuclear subalgebra; implementing coefficients
lie in the ambient ultrapower. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I]

def relativeCoefficientEnlargement (T : B → D) (a : I → D) (c : I → B) (b : B) : D :=
  ∑ i, ∑ j, star (a i) * T (star (c i) * b * c j) * a j

lemma relativeCoefficientEnlargement_inner (φ : B →⋆ₙₐ[ℂ] D)
    (a : I → D) (c : I → B) (d : D) (b : B) :
    relativeCoefficientEnlargement (innerHomCompression φ d) a c b =
      star (∑ i, φ (c i) * d * a i) * φ b * (∑ i, φ (c i) * d * a i) := by
  simp only [relativeCoefficientEnlargement, innerHomCompression_apply,
    map_mul, map_star, star_sum, Finset.sum_mul, Finset.mul_sum, star_mul, mul_assoc]
  exact Finset.sum_comm

lemma relativeCoefficientEnlargement_error_le (S T : B → D)
    (a : I → D) (c : I → B) (b : B) (δ : ℝ)
    (hST : ∀ i j, ‖S (star (c i) * b * c j) - T (star (c i) * b * c j)‖ ≤ δ) :
    ‖relativeCoefficientEnlargement S a c b - relativeCoefficientEnlargement T a c b‖ ≤
      δ * ∑ i, ∑ j, ‖a i‖ * ‖a j‖ := by
  have he : relativeCoefficientEnlargement S a c b - relativeCoefficientEnlargement T a c b =
      ∑ i, ∑ j, star (a i) * (S (star (c i) * b * c j) - T (star (c i) * b * c j)) * a j := by
    simp only [relativeCoefficientEnlargement, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, ‖∑ j, star (a i) * (S (star (c i) * b * c j) -
        T (star (c i) * b * c j)) * a j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖star (a i) * (S (star (c i) * b * c j) -
        T (star (c i) * b * c j)) * a j‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i‖ * δ * ‖a j‖ := by
      gcongr with i j
      calc
        _ ≤ (‖star (a i)‖ * ‖S (star (c i) * b * c j) -
            T (star (c i) * b * c j)‖) * ‖a j‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ _ := by rw [norm_star]; gcongr; exact hST i j
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma ApproximatelyOneStepAlong.coefficientEnlargement
    (φ : B →⋆ₙₐ[ℂ] D) {T : B → D} (hT : ApproximatelyOneStepAlong φ T)
    (a : I → D) (c : I → B) :
    ApproximatelyOneStepAlong φ (relativeCoefficientEnlargement T a c) := by
  classical
  intro F ε hε
  let K : ℝ := 1 + ∑ i, ∑ j, ‖a i‖ * ‖a j‖
  have hs : 0 ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ := by positivity
  have hK : 0 < K := by dsimp only [K]; linarith
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  let G := F.biUnion fun b => Finset.univ.biUnion fun i =>
    Finset.univ.image fun j => star (c i) * b * c j
  obtain ⟨d, hd⟩ := hT G δ hδ
  refine ⟨∑ i, φ (c i) * d * a i, ?_⟩
  intro b hb
  rw [← relativeCoefficientEnlargement_inner φ a c d b]
  have hpoint (i j : I) : ‖T (star (c i) * b * c j) -
      innerHomCompression φ d (star (c i) * b * c j)‖ ≤ δ := by
    exact (hd _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩⟩)).le
  apply (relativeCoefficientEnlargement_error_le T (innerHomCompression φ d) a c b δ hpoint).trans_lt
  have he : δ * K = ε := div_mul_cancel₀ ε hK.ne'
  dsimp only [K] at he
  nlinarith

end WeakPureInfiniteness

end

end OAI
