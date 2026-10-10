import OAI.Geometry.CylinderCovering.Angular.TableGeometry
import OAI.Geometry.CylinderCovering.Angular.GeneralFamilyCosts

namespace OAI

noncomputable section
namespace CylinderCovering.AngularTableGeometry

lemma lower_family_area_dilate {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    (∑ j : Fin D.count, TriangularCovering.area (lowerBase r τ D j)) =
      r^2 * ∑ j : Fin D.count, TriangularCovering.area (AngularGeneral.lowerBase τ D j) := by
  simp only [lowerBase,area_dilate hr,Finset.mul_sum]

lemma upper_family_area_dilate {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    (∑ j : Fin D.count, TriangularCovering.area (upperBase r τ D j)) =
      r^2 * ∑ j : Fin D.count, TriangularCovering.area (AngularGeneral.upperBase τ D j) := by
  simp only [upperBase,area_dilate hr,Finset.mul_sum]

lemma lower_family_area {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    (∑ j : Fin D.count, TriangularCovering.area (lowerBase r τ D j)) =
      totalArea r τ D / 2 := by
  rw [lower_family_area_dilate hr,AngularGeneral.lower_family_area,totalArea_dilate hr]
  ring

lemma upper_family_area {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    (∑ j : Fin D.count, TriangularCovering.area (upperBase r τ D j)) =
      totalArea r τ D / 2 := by
  rw [upper_family_area_dilate hr,AngularGeneral.upper_family_area,totalArea_dilate hr]
  ring

theorem separate_family_expansions {r τ η A : ℝ} {D : AngularGeneral.Data}
    (hr : r ≠ 0) (harea : |AngularGeneral.totalArea τ D / TriangularCovering.H -
      (1/2+(2*η-1/240)*τ^2)| ≤ A*τ^4) :
    |(∑ j : Fin D.count, TriangularCovering.area (lowerBase r τ D j)) /
        minimumShadowArea (body r) - (1/4+(η-1/480)*τ^2)| ≤ (A/2)*τ^4 ∧
    |(∑ j : Fin D.count, TriangularCovering.area (upperBase r τ D j)) /
        minimumShadowArea (body r) - (1/4+(η-1/480)*τ^2)| ≤ (A/2)*τ^4 := by
  rw [lower_family_area_dilate hr,upper_family_area_dilate hr,minimumShadowArea_body hr,
    mul_div_mul_left _ _ (pow_ne_zero 2 hr),mul_div_mul_left _ _ (pow_ne_zero 2 hr)]
  exact AngularGeneral.separate_family_expansions harea

private lemma physical_error {X H c B : ℝ} (hH : 0 < H)
    (h : |X/H-c| ≤ B) : |X-H*c| ≤ H*B := by
  have hid : X-H*c=H*(X/H-c) := by field_simp
  rw [hid,abs_mul,abs_of_pos hH]
  exact mul_le_mul_of_nonneg_left h hH.le

theorem cartesian_separate_family_expansions {lam A : ℝ} {D : AngularGeneral.Data}
    (harea : |AngularGeneral.totalArea (lam/2) D / TriangularCovering.H -
      (1/2+(2*(1/960:ℝ)-1/240)*(lam/2)^2)| ≤ A*(lam/2)^4) :
    |(∑ j : Fin D.count, TriangularCovering.area
        (lowerBase (1/TriangularCovering.H) (lam/2) D j)) -
      ((1/TriangularCovering.H)/4-(1/TriangularCovering.H)*lam^2/3840)| ≤
        (A/(32*TriangularCovering.H))*lam^4 ∧
    |(∑ j : Fin D.count, TriangularCovering.area
        (upperBase (1/TriangularCovering.H) (lam/2) D j)) -
      ((1/TriangularCovering.H)/4-(1/TriangularCovering.H)*lam^2/3840)| ≤
        (A/(32*TriangularCovering.H))*lam^4 := by
  have h := separate_family_expansions (r := 1/TriangularCovering.H)
    (one_div_ne_zero TriangularCovering.H_ne_zero) harea
  have hm : minimumShadowArea (body (1/TriangularCovering.H)) =
      1/TriangularCovering.H := by
    rw [minimumShadowArea_body (one_div_ne_zero TriangularCovering.H_ne_zero)]
    field_simp
  rw [hm] at h
  have h1 := physical_error (one_div_pos.mpr TriangularCovering.H_pos) h.1
  have h2 := physical_error (one_div_pos.mpr TriangularCovering.H_pos) h.2
  constructor
  · convert h1 using 1 <;> ring_nf
  · convert h2 using 1 <;> ring_nf

theorem squared_separate_family_expansions {n : ℕ} {A : ℝ} {D : AngularGeneral.Data}
    (harea : |AngularGeneral.totalArea (2/(n:ℝ)) D / TriangularCovering.H -
      (1/2+(2*(1/960:ℝ)-1/240)*(2/(n:ℝ))^2)| ≤ A*(2/(n:ℝ))^4) :
    |(∑ j : Fin D.count, TriangularCovering.area (lowerBase 1 (2/(n:ℝ)) D j)) -
      TriangularCovering.H*(1/4+(1/240-1/120)*(1/(n:ℝ))^2)| ≤
        8*TriangularCovering.H*A*(1/(n:ℝ))^4 ∧
    |(∑ j : Fin D.count, TriangularCovering.area (upperBase 1 (2/(n:ℝ)) D j)) -
      TriangularCovering.H*(1/4+(1/240-1/120)*(1/(n:ℝ))^2)| ≤
        8*TriangularCovering.H*A*(1/(n:ℝ))^4 := by
  have h := separate_family_expansions (r := 1) (by norm_num) harea
  rw [minimumShadowArea_body (by norm_num : (1:ℝ) ≠ 0)] at h
  norm_num only [one_pow,one_mul] at h
  have h1 := physical_error TriangularCovering.H_pos h.1
  have h2 := physical_error TriangularCovering.H_pos h.2
  constructor
  · convert h1 using 1 <;> ring_nf
  · convert h2 using 1 <;> ring_nf

end CylinderCovering.AngularTableGeometry

end

end OAI
