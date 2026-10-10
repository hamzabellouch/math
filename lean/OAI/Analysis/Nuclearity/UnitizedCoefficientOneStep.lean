import OAI.Analysis.Nuclearity.UnitizedCoefficients

namespace OAI

/-! The finite coefficient estimate and one-step implementation remain valid
for unitization coefficients. All implementing elements remain in D. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I]

lemma unitizedCoefficientEnlargement_error_le (S T : B → D)
    (a : I → Unitization ℂ D) (c : I → B) (b : B) (δ : ℝ)
    (hST : ∀ i j, ‖S (star (c i) * b * c j) - T (star (c i) * b * c j)‖ ≤ δ) :
    ‖unitizedCoefficientEnlargement S a c b - unitizedCoefficientEnlargement T a c b‖ ≤
      δ * ∑ i, ∑ j, ‖a i‖ * ‖a j‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ), Unitization.inr_sub,
    inr_unitizedCoefficientEnlargement, inr_unitizedCoefficientEnlargement]
  exact relativeCoefficientEnlargement_error_le
    (fun x => (S x : Unitization ℂ D)) (fun x => (T x : Unitization ℂ D)) a c b δ
    (fun i j => by simpa only [← Unitization.inr_sub, Unitization.norm_inr] using hST i j)

lemma ApproximatelyOneStepAlong.unitizedCoefficientEnlargement
    (φ : B →⋆ₙₐ[ℂ] D) {T : B → D} (hT : ApproximatelyOneStepAlong φ T)
    (a : I → Unitization ℂ D) (c : I → B) :
    ApproximatelyOneStepAlong φ (unitizedCoefficientEnlargement T a c) := by
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
  refine ⟨∑ i, unitizedRightMul (φ (c i) * d) (a i), ?_⟩
  intro b hb
  rw [← unitizedCoefficientEnlargement_inner φ a c d b]
  have hpoint (i j : I) : ‖T (star (c i) * b * c j) -
      innerHomCompression φ d (star (c i) * b * c j)‖ ≤ δ := by
    exact (hd _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩⟩)).le
  apply (unitizedCoefficientEnlargement_error_le T (innerHomCompression φ d) a c b δ hpoint).trans_lt
  have he : δ * K = ε := div_mul_cancel₀ ε hK.ne'
  dsimp only [K] at he
  nlinarith

end WeakPureInfiniteness

end

end OAI
