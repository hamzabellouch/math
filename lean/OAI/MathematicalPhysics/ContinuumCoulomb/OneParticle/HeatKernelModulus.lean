import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatKernel
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Quantitative bounds for the scalar heat-resolvent kernel away from
time zero. Every constant is elementary in the cutoff and radius. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

def exponent (t A : ℝ) : ℝ := -t - A / (4 * t)
def kernel (t A : ℝ) : ℝ := Real.exp (exponent t A) / (4 * Real.pi * t)

theorem kernel_eq_heat (t : ℝ) (r : PlanarPosition) :
    kernel t (‖r‖ ^ 2) = Real.exp (-t) * planarHeatKernel t r := by
  rw [kernel, exponent, sub_eq_add_neg, Real.exp_add, planarHeatKernel, neg_div]
  ring

theorem exp_nonpositive_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Set.Iic (0 : ℝ)) (C := 1)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_one_iff.mpr hz)
    (convex_Iic (0 : ℝ)) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem reciprocal_lipschitz {η t s : ℝ} (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) :
    |t⁻¹ - s⁻¹| ≤ |t - s| / η ^ 2 := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs0 : 0 < s := hη.trans_le hs
  have hid : t⁻¹ - s⁻¹ = (s - t) / (t * s) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos ht0 hs0), abs_sub_comm s t]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hs)])

theorem exponent_nonpositive {t A : ℝ} (ht : 0 < t) (hA : 0 ≤ A) :
    exponent t A ≤ 0 := by
  have h := div_nonneg hA (show 0 ≤ 4 * t by positivity)
  dsimp only [exponent]
  linarith

theorem exponent_time_lipschitz {η t s A : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hA : 0 ≤ A) :
    |exponent t A - exponent s A| ≤ (1 + A / (4 * η ^ 2)) * |t - s| := by
  have hid : exponent t A - exponent s A =
      -(t - s) - (A / 4) * (t⁻¹ - s⁻¹) := by unfold exponent; ring
  rw [hid]
  calc
    _ ≤ |-(t - s)| + |A / 4 * (t⁻¹ - s⁻¹)| := abs_sub _ _
    _ = |t - s| + A / 4 * |t⁻¹ - s⁻¹| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A / 4)]
    _ ≤ |t - s| + A / 4 * (|t - s| / η ^ 2) := by
      gcongr
      exact reciprocal_lipschitz hη ht hs
    _ = _ := by ring

theorem kernel_nonnegative {t A : ℝ} (ht : 0 < t) : 0 ≤ kernel t A := by
  unfold kernel
  positivity

theorem kernel_le_inverse {η t A : ℝ} (hη : 0 < η) (ht : η ≤ t) (hA : 0 ≤ A) :
    kernel t A ≤ η⁻¹ := by
  have ht0 : 0 < t := hη.trans_le ht
  have he : Real.exp (exponent t A) ≤ 1 :=
    Real.exp_le_one_iff.mpr (exponent_nonpositive ht0 hA)
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  calc
    kernel t A ≤ 1 / (4 * Real.pi * t) := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ 1 / η := div_le_div_of_nonneg_left (by norm_num) hη
      (by nlinarith [mul_le_mul_of_nonneg_right hp ht0.le])
    _ = _ := one_div _

theorem kernel_space_lipschitz {η t A B : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |kernel t A - kernel t B| ≤ |A - B| / η ^ 2 := by
  have ht0 : 0 < t := hη.trans_le ht
  have hq := exp_nonpositive_lipschitz (exponent_nonpositive ht0 hA)
    (exponent_nonpositive ht0 hB)
  have he : exponent t A - exponent t B = -(A - B) / (4 * t) := by
    unfold exponent
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (show 0 < 4 * t by positivity)] at hq
  have hd : 0 < 4 * Real.pi * t := by positivity
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  have hden : η ^ 2 ≤ (4 * t) * (4 * Real.pi * t) := by
    have ht1 : η ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hη.le ht0.le).mpr ht
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 4 * t ^ 2 by positivity)
    nlinarith
  calc
    |kernel t A - kernel t B| =
        |Real.exp (exponent t A) - Real.exp (exponent t B)| / (4 * Real.pi * t) := by
      rw [kernel, kernel, ← sub_div, abs_div, abs_of_pos hd]
    _ ≤ (|A - B| / (4 * t)) / (4 * Real.pi * t) :=
      div_le_div_of_nonneg_right hq hd.le
    _ = |A - B| / ((4 * t) * (4 * Real.pi * t)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

theorem kernel_time_lipschitz {η t s A : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hA : 0 ≤ A) :
    |kernel t A - kernel s A| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + A / (4 * η ^ 2))) * |t - s| := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs0 : 0 < s := hη.trans_le hs
  have hqt := exponent_nonpositive ht0 hA
  have hqs := exponent_nonpositive hs0 hA
  have hEt : Real.exp (exponent t A) ≤ 1 := Real.exp_le_one_iff.mpr hqt
  have he := (exp_nonpositive_lipschitz hqt hqs).trans (exponent_time_lipschitz hη ht hs hA)
  have hi := reciprocal_lipschitz hη ht hs
  have hsInv : s⁻¹ ≤ η⁻¹ := inv_anti₀ hη hs
  have hprod : |t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A)| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + A / (4 * η ^ 2))) * |t - s| := by
    have hid : t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A) =
        (t⁻¹ - s⁻¹) * Real.exp (exponent t A) +
        s⁻¹ * (Real.exp (exponent t A) - Real.exp (exponent s A)) := by ring
    rw [hid]
    calc
      _ ≤ |(t⁻¹ - s⁻¹) * Real.exp (exponent t A)| +
          |s⁻¹ * (Real.exp (exponent t A) - Real.exp (exponent s A))| := abs_add_le _ _
      _ = |t⁻¹ - s⁻¹| * Real.exp (exponent t A) +
          s⁻¹ * |Real.exp (exponent t A) - Real.exp (exponent s A)| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (inv_pos.mpr hs0)]
      _ ≤ |t - s| / η ^ 2 + η⁻¹ * ((1 + A / (4 * η ^ 2)) * |t - s|) := by
        apply add_le_add
        · exact (mul_le_of_le_one_right (abs_nonneg _) hEt).trans hi
        · exact mul_le_mul hsInv he (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hc : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  have hc1 : (4 * Real.pi)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    linarith [Real.two_le_pi]
  have hid : kernel t A - kernel s A = (4 * Real.pi)⁻¹ *
      (t⁻¹ * Real.exp (exponent t A) - s⁻¹ * Real.exp (exponent s A)) := by
    unfold kernel
    ring
  rw [hid, abs_mul, abs_of_nonneg hc]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans hprod

end ContinuumCoulomb.HeatKernelModulus

end

end OAI
