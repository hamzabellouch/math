import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace
namespace RegularSimplexSimilarity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem basis_isometry_of_gram {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c : Module.Basis ι ℝ F)
    (hgram : ∀ i j, inner ℝ (c i) (c j) = inner ℝ (b i) (b j)) :
    ∃ L : E ≃ₗᵢ[ℝ] F, ∀ i, L (b i) = c i := by
  classical
  let L := b.equiv c (Equiv.refl ι)
  have hL : ∀ i, L (b i) = c i := by
    intro i
    simp [L, Module.Basis.equiv_apply]
  have hexp (x : E) : L x = ∑ i, b.repr x i • c i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hL]
  have hinner : ∀ x y, inner ℝ (L x) (L y) = inner ℝ x y := by
    intro x y
    calc
      inner ℝ (L x) (L y) =
          inner ℝ (∑ i, b.repr x i • c i) (∑ j, b.repr y j • c j) := by
        rw [hexp, hexp]
      _ = inner ℝ (∑ i, b.repr x i • b i) (∑ j, b.repr y j • b j) := by
        simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hgram]
      _ = inner ℝ x y := by rw [b.sum_repr, b.sum_repr]
  exact ⟨L.isometryOfInner hinner, hL⟩

theorem affine_basis_congruence {ι : Type*} [Fintype ι]
    (p : AffineBasis ι ℝ E) (q : AffineBasis ι ℝ F) (i₀ : ι)
    (hdist : ∀ i j, dist (q i) (q j) = dist (p i) (p j)) :
    ∃ L : E ≃ₗᵢ[ℝ] F, ∃ t : F, ∀ i, q i = t + L (p i) := by
  classical
  have hgram : ∀ i j, inner ℝ (q.basisOf i₀ i) (q.basisOf i₀ j) =
      inner ℝ (p.basisOf i₀ i) (p.basisOf i₀ j) := by
    intro i j
    simp only [AffineBasis.basisOf_apply, vsub_eq_sub,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hdist]
  obtain ⟨L, hL⟩ := basis_isometry_of_gram (p.basisOf i₀) (q.basisOf i₀) hgram
  refine ⟨L, q i₀ - L (p i₀), ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    abel
  · have h := hL ⟨i, hi⟩
    simp only [AffineBasis.basisOf_apply, vsub_eq_sub, map_sub] at h
    calc
      q i = (q i - q i₀) + q i₀ := by abel
      _ = (L (p i) - L (p i₀)) + q i₀ := by rw [h]
      _ = q i₀ - L (p i₀) + L (p i) := by abel

theorem simplex_congruence {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    (hdist : ∀ i j, dist (q i) (q j) = dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n), ∀ i, q i = t + L (p i) := by
  let bp : AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n)) :=
    ⟨p, hp, hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩
  let bq : AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n)) :=
    ⟨q, hq, hq.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩
  exact affine_basis_congruence bp bq 0 hdist

theorem simplex_similarity {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i j, dist (q i) (q j) = r * dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n), ∀ i, q i = t + r • L (p i) := by
  have hp' : AffineIndependent ℝ (fun i => r • p i) := by
    simpa only [Function.comp_def, AffineMap.homothety_apply, vsub_eq_sub,
      sub_zero, vadd_eq_add, add_zero] using
      hp.map' (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin n)) r)
        (AffineMap.homothety_injective _ (ne_of_gt hr))
  have hd' : ∀ i j, dist (q i) (q j) = dist (r • p i) (r • p j) := by
    intro i j
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, hdist]
  obtain ⟨L, t, h⟩ := simplex_congruence (fun i => r • p i) q hp' hq hd'
  exact ⟨L, t, by simpa only [map_smul] using h⟩

theorem simplex_similarity_hull {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i j, dist (q i) (q j) = r * dist (p i) (p j)) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n),
        convexHull ℝ (range q) =
          CylinderCovering.Similarity.map t r L '' convexHull ℝ (range p) := by
  obtain ⟨L, t, h⟩ := simplex_similarity p q hp hq hr hdist
  refine ⟨L, t, ?_⟩
  let f := CylinderCovering.Similarity.affineMap t r L
  have hf : q = f ∘ p := by
    funext i
    exact h i
  rw [hf, range_comp, ← f.image_convexHull]
  rfl

theorem regular_simplex_similarity {n : ℕ}
    (p q : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpdist : ∀ i j, i ≠ j → dist (p i) (p j) = a)
    (hqdist : ∀ i j, i ≠ j → dist (q i) (q j) = b) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ t : EuclideanSpace ℝ (Fin n),
        convexHull ℝ (range q) =
          CylinderCovering.Similarity.map t (b / a) L '' convexHull ℝ (range p) := by
  apply simplex_similarity_hull p q hp hq (div_pos hb ha)
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [hpdist i j hij, hqdist i j hij, div_mul_cancel₀ _ (ne_of_gt ha)]

end RegularSimplexSimilarity

end

end OAI
