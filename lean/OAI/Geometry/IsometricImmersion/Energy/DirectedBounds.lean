import OAI.Geometry.IsometricImmersion.Energy.WeightPrimitive
import OAI.Geometry.IsometricImmersion.Energy.MultiplierAbsorption

namespace OAI

noncomputable section
open scoped ContDiff
namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

variable {B : Coord → ℝ} {R a b : ℝ} {p : Coord}

theorem primitive_directedT_lower_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (edge lambda epsilon MI MB : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB)
    (hlambda : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda) :
    directedWeight edge lambda (coordinatePrimitive B) p * weightH0 edge lambda p / 4 ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
        (directedN edge lambda epsilon (coordinatePrimitive B)) p := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hH : lambda ≤ weightH0 edge lambda p := by
    unfold weightH0
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) hd.le)
  have hbound := normalized_T_lower_bound heps hR.le hIs
    (abs_lt.mpr hp.1).le hBp (hlambda.trans hH)
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hcoeff := (directed_coefficients (fun _ => 0) B (fun _ => 0)
    edge lambda epsilon (differentiableAt_const (0 : ℝ)) hI hd.ne').1
  rw [coordinatePrimitive_partial_t hB hR hp] at hcoeff
  rw [hcoeff]
  have hm := mul_le_mul_of_nonneg_left hbound hW
  nlinarith only [hm]

theorem primitive_directedJ_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon MCA MA MI : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge) (hH : 0 ≤ weightH0 edge lambda p)
    (hCA : |C p - coordPartial 1 A p| ≤ MCA)
    (hAp : |A p| ≤ MA) (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI) :
    |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      directedWeight edge lambda (coordinatePrimitive B) p * epsilon * R *
        (MCA + MA * MI + weightH0 edge lambda p * |A p|) := by
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hprod : |A p * coordPartial 1 (coordinatePrimitive B) p| ≤ MA * MI := by
    rw [abs_mul]
    exact mul_le_mul hAp hIs (abs_nonneg _) hMA
  have hinner : |C p - coordPartial 1 A p +
      A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p)| ≤
      MCA + MA * MI + weightH0 edge lambda p * |A p| := by
    have he : C p - coordPartial 1 A p +
        A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p) =
        (C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p +
          weightH0 edge lambda p * A p := by ring
    rw [he]
    calc
      _ ≤ |(C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p| +
          |weightH0 edge lambda p * A p| := abs_add_le _ _
      _ ≤ (|C p - coordPartial 1 A p| +
          |A p * coordPartial 1 (coordinatePrimitive B) p|) +
          |weightH0 edge lambda p * A p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by
        rw [abs_mul (weightH0 edge lambda p) (A p), abs_of_nonneg hH]
        exact add_le_add (add_le_add hCA hprod) le_rfl
  rw [primitive_directedJ hB hR hp A C hA edge lambda epsilon hd.ne']
  simp only [abs_mul, abs_of_nonneg hW, abs_of_nonneg heps]
  have ht : |p 0| ≤ R := (abs_lt.mpr hp.1).le
  have hm := mul_le_mul ht hinner (abs_nonneg _) hR.le
  have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg hW heps)
  nlinarith only [hm']

end SmoothLocal.Weighted

end

end OAI
