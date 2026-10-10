import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section

open Set MeasureTheory

namespace CylinderCovering.CostComparison

lemma shadowArea_nonneg (K : Set Space) (u : Space) : 0 ≤ shadowArea K u :=
  ENNReal.toReal_nonneg

lemma minimumShadowArea_le_shadowArea (K : Set Space) (u : Space) (hu : ‖u‖ = 1) :
    minimumShadowArea K ≤ shadowArea K u := by
  unfold minimumShadowArea
  refine csInf_le ?_ ⟨u, hu, rfl⟩
  refine ⟨0, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  exact shadowArea_nonneg K v

theorem relativeCost_le_familyArea_div_minimum {n : ℕ} (K : Set Space)
    (C : Fin n → RuledApproximation.Cylinder) (hK : 0 < minimumShadowArea K) :
    relativeCost K C ≤ RuledApproximation.familyArea C / minimumShadowArea K := by
  unfold relativeCost RuledApproximation.familyArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hK
    (minimumShadowArea_le_shadowArea K (C i).axis (C i).unit_axis)

theorem relativeCost_lt_half_of_familyArea_lt_half {n : ℕ} (K : Set Space)
    (C : Fin n → RuledApproximation.Cylinder) (hK : 0 < minimumShadowArea K)
    (hC : RuledApproximation.familyArea C < minimumShadowArea K / 2) :
    relativeCost K C < 1 / 2 := by
  apply (relativeCost_le_familyArea_div_minimum K C hK).trans_lt
  apply (div_lt_iff₀ hK).2
  linarith

theorem triangularRelativeCost_le_totalArea_div_minimum {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) (hK : 0 < minimumShadowArea K) :
    triangularRelativeCost K C ≤ TriangularCovering.totalArea C / minimumShadowArea K := by
  unfold triangularRelativeCost TriangularCovering.totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hK
    (minimumShadowArea_le_shadowArea K (C i).axis (C i).unit_axis)

theorem triangularRelativeCost_lt_half_of_totalArea_lt_half {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) (hK : 0 < minimumShadowArea K)
    (hC : TriangularCovering.totalArea C < minimumShadowArea K / 2) :
    triangularRelativeCost K C < 1 / 2 := by
  apply (triangularRelativeCost_le_totalArea_div_minimum K C hK).trans_lt
  apply (div_lt_iff₀ hK).2
  linarith

end CylinderCovering.CostComparison

end

end OAI
