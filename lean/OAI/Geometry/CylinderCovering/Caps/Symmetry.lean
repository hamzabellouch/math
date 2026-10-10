import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite

def familyIsometry : Space ≃ₗᵢ[ℝ] Space where
  toFun z := !₂[z 1, -z 0, -z 2]
  invFun z := !₂[-z 1, z 0, -z 2]
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c z := by ext i; fin_cases i <;> simp
  norm_map' z := by
    change ‖(!₂[z 1, -z 0, -z 2] : Space)‖ = ‖z‖
    have hsq : ‖(!₂[z 1, -z 0, -z 2] : Space)‖ ^ 2 = ‖z‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      ring
    nlinarith [norm_nonneg (!₂[z 1, -z 0, -z 2] : Space), norm_nonneg z]

def familyTranslation : Space := !₂[0,0,height]

lemma secondRaw_isometry (δ r : ℝ) :
    secondRaw δ r = -familyIsometry (firstRaw δ r) := by
  ext i
  fin_cases i <;> simp [secondRaw, firstRaw, familyIsometry]

lemma secondAxis_isometry (δ r : ℝ) :
    secondAxis δ r = -familyIsometry (firstAxis δ r) := by
  rw [secondAxis, secondRaw_isometry]
  simp [firstAxis]

lemma secondFoot_isometry (p : ℝ × ℝ) :
    secondFoot p = Similarity.map familyTranslation 1 familyIsometry (firstFoot p) := by
  ext i
  fin_cases i <;> simp [secondFoot, firstFoot, Similarity.map,
    familyTranslation, familyIsometry]
  ring

lemma projection_neg_axis (u z : Space) :
    TriangularCovering.projection (-u) z = TriangularCovering.projection u z := by
  simp [TriangularCovering.projection]

theorem secondBase_transported (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    secondBase δ R N i = Similarity.transportedBase (firstBase δ R N i)
      (firstAxis δ (midpoint N i)) familyTranslation 1 familyIsometry := by
  unfold secondBase firstBase Similarity.transportedBase
  rw [image_image, image_image, image_image]
  congr 1
  funext p
  simp only [secondAxis_isometry, projection_neg_axis,
    secondFoot_isometry]
  exact Similarity.project_map (firstAxis δ (midpoint N i)) familyTranslation
    (firstFoot p) 1 familyIsometry

theorem secondBase_area_eq (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    TriangularCovering.area (secondBase δ R N i) =
      TriangularCovering.area (firstBase δ R N i) := by
  rw [secondBase_transported]
  change Similarity.area _ = Similarity.area _
  rw [Similarity.area_transportedBase _ _ _ (by norm_num : (1 : ℝ) ≠ 0)]
  simp

theorem secondBase_properties_of_first {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} {i : Fin N}
    (h : BaseProperties (firstAxis δ (midpoint N i)) (firstBase δ R N i)) :
    BaseProperties (secondAxis δ (midpoint N i)) (secondBase δ R N i) := by
  rcases h with ⟨hu, hc, hv, hm, hf, hp⟩
  have hc' := Similarity.transportedBase_compact hc
    (firstAxis δ (midpoint N i)) familyTranslation 1 familyIsometry
  rw [secondBase_transported]
  refine ⟨?_, hc', Similarity.transportedBase_convex hv _ _ _ _, hc'.measurableSet,
    Similarity.transportedBase_finite hf _ _ (by norm_num : (1 : ℝ) ≠ 0) _, ?_⟩
  · rw [secondAxis_isometry, norm_neg, familyIsometry.norm_map]
    exact hu
  · intro z hz
    rw [secondAxis_isometry, inner_neg_left]
    rw [Similarity.transportedBase_perpendicular hu hp familyTranslation 1 familyIsometry z hz]
    simp

theorem totalArea_eq_twice_first (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) :
    totalArea δ R N = 2 * ∑ i : Fin N, TriangularCovering.area (firstBase δ R N i) := by
  unfold totalArea
  simp_rw [secondBase_area_eq]
  ring

end CylinderCovering.HalfheightFinite

end

end OAI
