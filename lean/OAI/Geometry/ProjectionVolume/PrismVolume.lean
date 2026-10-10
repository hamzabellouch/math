import OAI.Geometry.ProjectionVolume.ProductReconstruction
import OAI.Geometry.ProjectionVolume.FacetLinearImage
import OAI.Geometry.ProjectionVolume.SimplexCoordinates
import OAI.Geometry.ProjectionVolume.SimplexVolume

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise

namespace Paper092

def orthogonalPrismMap {m n : ℕ} (f : Euclidean m →ₗᵢ[ℝ] Euclidean n)
    (v : Euclidean n) : Euclidean (m + 1) →ₗ[ℝ] Euclidean n where
  toFun x := f (splitEuclideanProduct m 1 x).1 + ((splitEuclideanProduct m 1 x).2 0) • v
  map_add' x y := by simp only [map_add, Prod.fst_add, Prod.snd_add, PiLp.add_apply, add_smul]; abel
  map_smul' t x := by
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, smul_add,
      smul_smul, RingHom.id_apply]

theorem orthogonalPrismMap_inner {m n : ℕ} (f : Euclidean m →ₗᵢ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) (hf : ∀ x, ⟪v, f x⟫ = 0)
    (x y : Euclidean (m + 1)) :
    ⟪orthogonalPrismMap f v x, orthogonalPrismMap f v y⟫ = ⟪x, y⟫ := by
  have hfv (a : Euclidean m) : ⟪f a, v⟫ = 0 := by rw [real_inner_comm, hf]
  have hone (a b : Euclidean 1) : ⟪a, b⟫ = a 0 * b 0 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [splitEuclideanProduct_inner m 1 x y]
  change ⟪f (splitEuclideanProduct m 1 x).1 + ((splitEuclideanProduct m 1 x).2 0) • v,
    f (splitEuclideanProduct m 1 y).1 + ((splitEuclideanProduct m 1 y).2 0) • v⟫ = _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    f.inner_map_map, hf, hfv, real_inner_self_eq_norm_sq, hv, one_pow, mul_zero, zero_add,
    add_zero, mul_one, hone]
  ring

def orthogonalPrismEmbedding {m n : ℕ} (f : Euclidean m →ₗᵢ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) (hf : ∀ x, ⟪v, f x⟫ = 0) :
    Euclidean (m + 1) →ₗᵢ[ℝ] Euclidean n where
  toLinearMap := orthogonalPrismMap f v
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact orthogonalPrismMap_inner f v hv hf x x

theorem mem_standardSimplex_one (x : Euclidean 1) :
    x ∈ standardSimplex 1 ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  simp [mem_standardSimplex_iff, Fin.forall_fin_one]

theorem orthogonalPrismMap_image {m n : ℕ} (f : Euclidean m →ₗᵢ[ℝ] Euclidean n)
    (v : Euclidean n) (A : Set (Euclidean m)) :
    orthogonalPrismMap f v '' cartesianBody A (standardSimplex 1) =
      f '' A + segment ℝ 0 v := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨f (splitEuclideanProduct m 1 x).1, ⟨_, hx.1, rfl⟩,
      ((splitEuclideanProduct m 1 x).2 0) • v, ?_, rfl⟩
    rw [segment_eq_image]
    refine ⟨(splitEuclideanProduct m 1 x).2 0, (mem_standardSimplex_one _).mp hx.2, ?_⟩
    simp
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    rw [segment_eq_image] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    let y : Euclidean 1 := WithLp.toLp 2 (fun _ => t)
    refine ⟨(splitEuclideanProduct m 1).symm (x, y), ?_, ?_⟩
    · rw [cartesianBody_eq_preimage, Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨hx, (mem_standardSimplex_one y).mpr ht⟩
    · change f (splitEuclideanProduct m 1 ((splitEuclideanProduct m 1).symm (x, y))).1 +
          ((splitEuclideanProduct m 1 ((splitEuclideanProduct m 1).symm (x, y))).2 0) • v = _
      simp [y]

theorem orthogonalPrism_volume {m n : ℕ} (f : Euclidean m →ₗᵢ[ℝ] Euclidean n)
    (v : Euclidean n) (hv : ‖v‖ = 1) (hf : ∀ x, ⟪v, f x⟫ = 0) (hdim : m + 1 = n)
    (A : Set (Euclidean m)) (hA : MeasurableSet A) :
    volume (f '' A + segment ℝ 0 v) = volume A := by
  let g := orthogonalPrismEmbedding f v hv hf
  have h := g.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (cartesianBody A (standardSimplex 1))
  simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
    ENNReal.ofReal_one, one_mul] at h
  change μHE[m + 1] (orthogonalPrismMap f v '' cartesianBody A (standardSimplex 1)) = _ at h
  rw [orthogonalPrismMap_image, cartesianBody_volume _ _ hA
    (standardSimplex_isCompact 1).measurableSet, standardSimplex_volume] at h
  norm_num at h
  rw [hdim, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h

end Paper092

end

end OAI
