import OAI.Geometry.CylinderCovering.Angular.GeneralVolume

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.AngularGeneral

lemma lower_area_eq_upper_area (τ : ℝ) (D : Data) (j : ℕ) :
    TriangularCovering.area (lowerBase τ D j) =
      TriangularCovering.area (upperBase τ D j) := by
  rw [lowerBase_area,upperBase_area]

lemma lower_family_area (τ : ℝ) (D : Data) :
    (∑ j : Fin D.count, TriangularCovering.area (lowerBase τ D j)) =
      totalArea τ D / 2 := by
  unfold totalArea
  simp only [← lower_area_eq_upper_area,← two_mul,← Finset.mul_sum]
  ring

lemma upper_family_area (τ : ℝ) (D : Data) :
    (∑ j : Fin D.count, TriangularCovering.area (upperBase τ D j)) =
      totalArea τ D / 2 := by
  simp only [← lower_area_eq_upper_area]
  exact lower_family_area τ D

lemma lower_family_integral {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) :
    (∑ j : Fin D.count, TriangularCovering.area (lowerBase τ D j)) /
        TriangularCovering.H = integralCost τ D / 2 := by
  rw [lower_family_area,div_right_comm,totalArea_div_H_eq_integralCost hD]

lemma upper_family_integral {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) :
    (∑ j : Fin D.count, TriangularCovering.area (upperBase τ D j)) /
        TriangularCovering.H = integralCost τ D / 2 := by
  rw [upper_family_area,div_right_comm,totalArea_div_H_eq_integralCost hD]

theorem separate_family_expansions {τ η A : ℝ} {D : Data}
    (harea : |totalArea τ D / TriangularCovering.H -
      (1/2+(2*η-1/240)*τ^2)| ≤ A*τ^4) :
    |(∑ j : Fin D.count, TriangularCovering.area (lowerBase τ D j)) /
        TriangularCovering.H - (1/4+(η-1/480)*τ^2)| ≤ (A/2)*τ^4 ∧
    |(∑ j : Fin D.count, TriangularCovering.area (upperBase τ D j)) /
        TriangularCovering.H - (1/4+(η-1/480)*τ^2)| ≤ (A/2)*τ^4 := by
  have hid : totalArea τ D / 2 / TriangularCovering.H -
      (1/4+(η-1/480)*τ^2) =
      (totalArea τ D / TriangularCovering.H - (1/2+(2*η-1/240)*τ^2))/2 := by ring
  rw [lower_family_area,upper_family_area,hid,abs_div]
  norm_num
  linarith only [harea]

end CylinderCovering.AngularGeneral

end

end OAI
