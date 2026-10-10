import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.TriangularCovering.Main

namespace OAI

open Set
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.RegularSimilarity

theorem exists_isometry_map_basis
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E) (f : ι → E)
    (hgram : ∀ i j, inner ℝ (f i) (f j) = inner ℝ (b i) (b j)) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ i, R (b i) = f i := by
  classical
  let L : E →ₗ[ℝ] E := b.constr ℝ f
  have hrep (x : E) : L x = ∑ i, b.repr x i • f i := by
    rw [← b.sum_repr x]
    simp [L]
  have hinner : ∀ x y, inner ℝ (L x) (L y) = inner ℝ x y := by
    intro x y
    rw [hrep, hrep]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      conj_trivial, hgram]
  let I := L.isometryOfInner hinner
  let R := LinearIsometryEquiv.ofSurjective I
    (LinearMap.surjective_of_injective I.injective)
  refine ⟨R, ?_⟩
  intro i
  change L (b i) = f i
  simp [L]

theorem exists_isometry_map_affineBasis
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E) (i₀ : ι) (q : ι → E)
    (hdist : ∀ i j, dist (q i) (q j) = dist (b i) (b j)) :
    ∃ a : E, ∃ R : E ≃ₗᵢ[ℝ] E, ∀ i, q i = a + R (b i) := by
  classical
  let f : {j : ι // j ≠ i₀} → E := fun j => q j - q i₀
  have hn (i j : ι) : ‖q i - q j‖ = ‖b i - b j‖ := by
    simpa only [dist_eq_norm] using hdist i j
  have hgram : ∀ i j, inner ℝ (f i) (f j) =
      inner ℝ (b.basisOf i₀ i) (b.basisOf i₀ j) := by
    intro i j
    simp only [f, AffineBasis.basisOf_apply, vsub_eq_sub]
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    rw [show (q i - q i₀) - (q j - q i₀) = q i - q j by abel,
      show (b i - b i₀) - (b j - b i₀) = b i - b j by abel]
    rw [hn, hn, hn]
  obtain ⟨R, hR⟩ := exists_isometry_map_basis (b.basisOf i₀) f hgram
  refine ⟨q i₀ - R (b i₀), R, ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    abel
  · have h := hR ⟨i, hi⟩
    simp only [AffineBasis.basisOf_apply, vsub_eq_sub, f, map_sub] at h
    calc
      q i = (q i - q i₀) + q i₀ := by abel
      _ = (R (b i) - R (b i₀)) + q i₀ := by rw [h]
      _ = q i₀ - R (b i₀) + R (b i) := by abel

theorem exists_similarity_map_affineBasis
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E) (i₀ : ι) (q : ι → E)
    {s : ℝ} (hs : 0 < s)
    (hdist : ∀ i j, dist (q i) (q j) = s * dist (b i) (b j)) :
    ∃ a : E, ∃ R : E ≃ₗᵢ[ℝ] E, ∀ i, q i = a + s • R (b i) := by
  let q' : ι → E := fun i => s⁻¹ • q i
  have hq' : ∀ i j, dist (q' i) (q' j) = dist (b i) (b j) := by
    intro i j
    dsimp [q']
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hs, ← dist_eq_norm, hdist]
    field_simp
  obtain ⟨a, R, hR⟩ := exists_isometry_map_affineBasis b i₀ q' hq'
  refine ⟨s • a, R, ?_⟩
  intro i
  have h := congrArg (fun x : E => s • x) (hR i)
  simpa only [q', smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul] using h

theorem regularTetrahedron_similarity {K : Set Space} (hK : IsRegularTetrahedron K) :
    ∃ a : Space, ∃ s : ℝ, 0 < s ∧ ∃ R : Space ≃ₗᵢ[ℝ] Space,
      K = (fun x => a + s • R x) '' TriangularCovering.K := by
  classical
  obtain ⟨v, hv, edge, hedge, hdist, rfl⟩ := hK
  have hspan : affineSpan ℝ (range TriangularCovering.tetraVertices) = ⊤ := by
    apply TriangularCovering.tetra_affineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp
  let b : AffineBasis (Fin 4) ℝ Space :=
    ⟨TriangularCovering.tetraVertices, TriangularCovering.tetra_affineIndependent, hspan⟩
  have hs : 0 < edge / 2 := by positivity
  have hd : ∀ i j, dist (v i) (v j) = (edge / 2) * dist (b i) (b j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · change dist (v i) (v j) = (edge / 2) *
        dist (TriangularCovering.tetraVertices i) (TriangularCovering.tetraVertices j)
      rw [hdist i j hij, TriangularCovering.tetra_edge_length hij]
      ring
  obtain ⟨a, R, hR⟩ := exists_similarity_map_affineBasis b 0 v hs hd
  refine ⟨a, edge / 2, hs, R, ?_⟩
  let F : Space →ᵃ[ℝ] Space :=
    AffineMap.const ℝ Space a + (edge / 2) • R.toLinearMap.toAffineMap
  have hF : ∀ x, F x = a + (edge / 2) • R x := by intro x; rfl
  have himage : F '' range TriangularCovering.tetraVertices = range v := by
    rw [← range_comp]
    congr 1
    funext i
    exact (hR i).symm
  calc
    convexHull ℝ (range v) = convexHull ℝ (F '' range TriangularCovering.tetraVertices) := by rw [himage]
    _ = F '' convexHull ℝ (range TriangularCovering.tetraVertices) := (F.image_convexHull _).symm
    _ = (fun x => a + (edge / 2) • R x) '' TriangularCovering.K := by
      rw [← TriangularCovering.K_eq_convexHull]
      rfl

end CylinderCovering.RegularSimilarity

end

end OAI
