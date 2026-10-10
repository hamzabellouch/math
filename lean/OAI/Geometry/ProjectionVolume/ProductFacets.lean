import OAI.Geometry.ProjectionVolume.ExposedProduct
import OAI.Geometry.ProjectionVolume.ExposedBounds

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem vectorSpan_finrank_of_interior_nonempty {n : ℕ} (K : Set (Euclidean n))
    (hint : (interior K).Nonempty) : Module.finrank ℝ (vectorSpan ℝ K) = n := by
  have hspan : affineSpan ℝ K = ⊤ := by
    have h := affineSpan_mono ℝ (interior_subset (s := K))
    rw [isOpen_interior.affineSpan_eq_top hint] at h
    exact top_unique h
  rw [← direction_affineSpan, hspan, AffineSubspace.direction_top,
    finrank_top, finrank_euclideanSpace_fin]

theorem exposedFace_product_codimension_two {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (w : Euclidean (r + s))
    (hu : (splitEuclideanProduct r s w).1 ≠ 0) (hv : (splitEuclideanProduct r s w).2 ≠ 0) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace (cartesianBody A B) w)) ≤ r + s - 2 := by
  rw [exposedFace_product, cartesianBody_affine_dimension _ _
    (exposedFace_nonempty A hA hAn _) (exposedFace_nonempty B hB hBn _)]
  have ha := exposedFace_finrank_le A hu
  have hb := exposedFace_finrank_le B hv
  omega

theorem exposedFace_productLiftLeft {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (u : Euclidean r) :
    exposedFace (cartesianBody A B) (productLiftLeft r s u) = cartesianBody (exposedFace A u) B := by
  rw [exposedFace_product, split_productLiftLeft, exposedFace_zero]

theorem exposedFace_productLiftRight {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (v : Euclidean s) :
    exposedFace (cartesianBody A B) (productLiftRight r s v) = cartesianBody A (exposedFace B v) := by
  rw [exposedFace_product, split_productLiftRight, exposedFace_zero]

theorem exposedFace_product_facet_classification {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hA : IsCompact A) (hB : IsCompact B)
    (hiA : (interior A).Nonempty) (hiB : (interior B).Nonempty) (w : Euclidean (r + s))
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace (cartesianBody A B) w)) = r + s - 1) :
    ((splitEuclideanProduct r s w).1 ≠ 0 ∧ (splitEuclideanProduct r s w).2 = 0 ∧
      Module.finrank ℝ (vectorSpan ℝ (exposedFace A (splitEuclideanProduct r s w).1)) = r - 1 ∧
      exposedFace (cartesianBody A B) w = cartesianBody
        (exposedFace A (splitEuclideanProduct r s w).1) B) ∨
    ((splitEuclideanProduct r s w).1 = 0 ∧ (splitEuclideanProduct r s w).2 ≠ 0 ∧
      Module.finrank ℝ (vectorSpan ℝ (exposedFace B (splitEuclideanProduct r s w).2)) = s - 1 ∧
      exposedFace (cartesianBody A B) w = cartesianBody A
        (exposedFace B (splitEuclideanProduct r s w).2)) := by
  have hnA : A.Nonempty := hiA.mono interior_subset
  have hnB : B.Nonempty := hiB.mono interior_subset
  have heq := cartesianBody_affine_dimension
    (exposedFace A (splitEuclideanProduct r s w).1)
    (exposedFace B (splitEuclideanProduct r s w).2)
    (exposedFace_nonempty A hA hnA _) (exposedFace_nonempty B hB hnB _)
  rw [← exposedFace_product] at heq
  have hArank := vectorSpan_finrank_of_interior_nonempty A hiA
  have hBrank := vectorSpan_finrank_of_interior_nonempty B hiB
  by_cases hu : (splitEuclideanProduct r s w).1 = 0
  · by_cases hv : (splitEuclideanProduct r s w).2 = 0
    · rw [hu, hv, exposedFace_zero, exposedFace_zero, hArank, hBrank] at heq
      omega
    · right
      refine ⟨hu, hv, ?_, ?_⟩
      · rw [hu, exposedFace_zero, hArank] at heq
        omega
      · rw [exposedFace_product, hu, exposedFace_zero]
  · by_cases hv : (splitEuclideanProduct r s w).2 = 0
    · left
      refine ⟨hu, hv, ?_, ?_⟩
      · rw [hv, exposedFace_zero, hBrank] at heq
        omega
      · rw [exposedFace_product, hv, exposedFace_zero]
    · have hcodim := exposedFace_product_codimension_two hr hs A B hA hB hnA hnB w hu hv
      omega

theorem exposedFace_product_facet_left {r s : ℕ} (hr : 0 < r)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hA : IsCompact A)
    (hnA : A.Nonempty) (hiB : (interior B).Nonempty) (u : Euclidean r)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace A u)) = r - 1) :
    Module.finrank ℝ (vectorSpan ℝ
      (exposedFace (cartesianBody A B) (productLiftLeft r s u))) = r + s - 1 := by
  rw [exposedFace_productLiftLeft, cartesianBody_affine_dimension _ _
    (exposedFace_nonempty A hA hnA _) (hiB.mono interior_subset),
    hdim, vectorSpan_finrank_of_interior_nonempty B hiB]
  omega

theorem exposedFace_product_facet_right {r s : ℕ} (hs : 0 < s)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hB : IsCompact B)
    (hiA : (interior A).Nonempty) (hnB : B.Nonempty) (v : Euclidean s)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace B v)) = s - 1) :
    Module.finrank ℝ (vectorSpan ℝ
      (exposedFace (cartesianBody A B) (productLiftRight r s v))) = r + s - 1 := by
  rw [exposedFace_productLiftRight, cartesianBody_affine_dimension _ _
    (hiA.mono interior_subset) (exposedFace_nonempty B hB hnB _),
    vectorSpan_finrank_of_interior_nonempty A hiA, hdim]
  omega

end Paper092

end

end OAI
