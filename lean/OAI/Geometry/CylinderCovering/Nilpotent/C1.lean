import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RuledApproximation

theorem nilpotentC1 :
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear 1 D G →
    (∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0) →
    ∀ h eps : ℝ, 0 < h → 0 < eps →
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D G 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (G b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i)) := by
  intro D G hD hG hnil h eps hh heps
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh hD hG hnil (mul_pos hh heps)
  choose T g hT hCT using hC
  refine ⟨n,T,g,hT,?_,?_,?_⟩
  · intro z hz
    have hz' : firstPhysicalMap h z ∈ physicalRuled h D G 1 := by
      rw [← firstPhysicalMap_ruled]
      exact mem_image_of_mem _ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hz')
    rw [hCT i,projectedCylinder_carrier] at hi
    obtain ⟨x,hx,hx'⟩ := hi
    have he : x = z := firstPhysicalMap_injective hh.ne' hx'
    exact mem_iUnion.mpr ⟨i, he ▸ hx⟩
  · simp_rw [familyArea,hCT,projectedCylinder_area hh] at hcost
    have he : (∑ i, h * volume.real (T i) * physicalWeight h (g i)) =
        h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hcost
    nlinarith
  · intro a
    let C₁ : Fin n → Cylinder := fun i => projectedCylinder h (g i) (T i)
    let C₂ : Fin n → Cylinder := fun i =>
      ((C₁ i).rotate swapReflect).translate (vec3 0 0 (h*a))
    refine ⟨C₁,C₂,fun i => ?_⟩
    have hP : (C₁ i).parallelogram := projectedCylinder_parallelogram hh _ (hT i).parallelogram
    refine ⟨hP,Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hP swapReflect) _,
      projectedCylinder_carrier h _ _,?_,projectedCylinder_area hh _ _,?_⟩
    · dsimp only [C₂]
      rw [Cylinder.translate_carrier,Cylinder.rotate_carrier,projectedCylinder_carrier,
        ← image_comp,← image_comp]
      congr 1
      funext z
      exact (physicalMaps_relation h a z).symm
    · dsimp only [C₂]
      rw [Cylinder.translate_area,Cylinder.rotate_area]
      exact projectedCylinder_area hh _ _

end RuledApproximation

end

end OAI
