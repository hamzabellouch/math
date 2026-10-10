import OAI.Geometry.CylinderCovering.Convexity.RegularBaseVariants
import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogramComparison

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering

theorem openParallelogramCounterexample_of_parallelogram {S : Set Space} {n : ℕ}
    (C : Fin n → RuledApproximation.Cylinder)
    (hC : ∀ i, (C i).parallelogram)
    (hcover : S ⊆ RuledApproximation.familySet C)
    (hcost : RuledApproximation.familyArea C < minimumShadowArea S / 2) :
    ∃ D : Fin n → RuledApproximation.Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openParallelogram ∧ (D i).openBounded) ∧
      S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  have hnonneg : 0 ≤ RuledApproximation.familyArea C :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hmin : 0 < minimumShadowArea S := by linarith
  have hshadow : ∀ i, minimumShadowArea S ≤ (C i).shadowArea S := by
    intro i
    rw [RuledApproximation.Cylinder.shadowArea_eq_global]
    exact Similarity.minimumArea_le_shadowArea S (C i).unit_axis
  obtain ⟨D, haxis, hshape, hcov, harea, hrelative⟩ :=
    RuledApproximation.openParallelogram_of_strict_half C S hC hcover hmin hshadow hcost
  rw [RuledApproximation.familyRelativeArea_eq_global] at hrelative
  exact ⟨D, haxis, hshape, hcov, harea, hrelative⟩

theorem regularOpenParallelogramCounterexample_result :
    ∀ K : Set Space, IsRegularTetrahedron K →
      ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
        (∀ i, (C i).openParallelogram ∧ (C i).openBounded) ∧
        K ⊆ RuledApproximation.familySet C ∧
        RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧
        relativeCost K C < 1 / 2 := by
  intro K hK
  obtain ⟨n, C, hshape, hcover, hcost, _⟩ := regularParallelogramCounterexample_result K hK
  obtain ⟨D, _, hshapeD, hcoverD, hcostD, hrelativeD⟩ :=
    openParallelogramCounterexample_of_parallelogram C hshape hcover hcost
  exact ⟨n, D, hshapeD, hcoverD, hcostD, hrelativeD⟩

end CylinderCovering

end

end OAI
