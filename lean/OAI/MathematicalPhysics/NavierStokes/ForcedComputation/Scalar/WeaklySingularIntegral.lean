import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! Exact integrability and norm bounds for an inverse-square-root Volterra kernel. -/

noncomputable section
namespace ForcedComputation.WeaklySingular

open Real MeasureTheory Set
open scoped Topology Interval

def inverseSqrt (r : ℝ) : ℝ := (Real.sqrt r)⁻¹

theorem inverseSqrt_nonneg (r : ℝ) : 0 ≤ inverseSqrt r :=
  inv_nonneg.mpr (Real.sqrt_nonneg r)

theorem inverseSqrt_eq_rpow {r : ℝ} (hr : 0 ≤ r) :
    inverseSqrt r = r ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hr, ← Real.sqrt_eq_rpow]
  rfl

theorem inverseSqrt_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable inverseSqrt volume 0 t := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  apply hi.congr
  intro r hr
  rw [uIoc_of_le ht] at hr
  exact (inverseSqrt_eq_rpow hr.1.le).symm

theorem integral_inverseSqrt {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in 0..t, inverseSqrt r) = 2 * Real.sqrt t := by
  calc
    _ = ∫ r in 0..t, r ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht] at hr
      exact inverseSqrt_eq_rpow hr.1
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
      norm_num
      rw [← Real.sqrt_eq_rpow]
      ring

theorem inverseSqrt_sub_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => inverseSqrt (t - s)) volume 0 t := by
  simpa only [sub_zero, sub_self] using (inverseSqrt_intervalIntegrable ht).comp_sub_left t |>.symm

theorem integral_inverseSqrt_sub {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, inverseSqrt (t - s)) = 2 * Real.sqrt t := by
  rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero, integral_inverseSqrt ht]

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A measurable integrand dominated by the inverse-square-root kernel is integrable. -/
theorem intervalIntegrable_of_inverseSqrt_bound {t : ℝ} (ht : 0 ≤ t)
    (f : ℝ → E) (B : ℝ) (hm : AEStronglyMeasurable f (volume.restrict (Ioc 0 t)))
    (hb : ∀ s ∈ Ioc 0 t, ‖f s‖ ≤ B * inverseSqrt (t - s)) :
    IntervalIntegrable f volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  apply (((inverseSqrt_sub_intervalIntegrable ht).const_mul B).1).mono' hm
  exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hb s hs

/-- The exact square-root norm bound, including the zero-time endpoint. -/
theorem norm_integral_le_inverseSqrt {t : ℝ} (ht : 0 ≤ t) (f : ℝ → E) (B : ℝ)
    (hb : ∀ s ∈ Ioc 0 t, ‖f s‖ ≤ B * inverseSqrt (t - s)) :
    ‖∫ s in 0..t, f s‖ ≤ 2 * B * Real.sqrt t := by
  calc
    _ ≤ ∫ s in 0..t, B * inverseSqrt (t - s) :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (ae_of_all _ fun s hs => hb s hs) ((inverseSqrt_sub_intervalIntegrable ht).const_mul B)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inverseSqrt_sub ht]
      ring

/-- The actual Volterra integral for an operator-valued kernel and a source curve. -/
def volterra (K : ℝ → E →L[ℝ] E) (u : ℝ → E) (t : ℝ) : E :=
  ∫ s in 0..t, K (t - s) (u s)

theorem norm_volterra_le {t : ℝ} (ht : 0 ≤ t)
    (K : ℝ → E →L[ℝ] E) (u : ℝ → E) (C B : ℝ) (hC : 0 ≤ C)
    (hK : ∀ r ∈ Icc 0 t, ‖K r‖ ≤ C * inverseSqrt r)
    (hu : ∀ s ∈ Icc 0 t, ‖u s‖ ≤ B) :
    ‖volterra E K u t‖ ≤ 2 * C * B * Real.sqrt t := by
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖K (t - s) (u s)‖ ≤ (C * B) * inverseSqrt (t - s) := by
    have hr : t - s ∈ Icc 0 t := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
    calc
      _ ≤ ‖K (t - s)‖ * ‖u s‖ := (K (t - s)).le_opNorm (u s)
      _ ≤ (C * inverseSqrt (t - s)) * B :=
        mul_le_mul (hK _ hr) (hu s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)
          (mul_nonneg hC (inverseSqrt_nonneg _))
      _ = _ := by ring
  simpa only [volterra, mul_assoc] using norm_integral_le_inverseSqrt E ht
    (fun s => K (t - s) (u s)) (C * B) hb

end ForcedComputation.WeaklySingular

end

end OAI
