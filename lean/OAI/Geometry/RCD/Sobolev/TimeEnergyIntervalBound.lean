import OAI.Geometry.RCD.Sobolev.SmoothTimeTestOrder
import OAI.Geometry.RCD.Heat.LipschitzTimePairing

namespace OAI

/-! # From smooth time tests to the energy bound on an interior interval -/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates

theorem time_energy_interval_bound
    {a b c r : ℝ} (hr : 0 < r) (ha : a < c-r) (hb : c+r < b)
    (P E : ℝ → ℝ) {L : ℝ≥0} (hP : LipschitzOnWith L P (Ioo a b))
    (hE : IntegrableOn E (Ioo a b))
    (htest : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b → (∀ t, 0 ≤ θ t) →
      (∫ t in Ioo a b, θ t*E t) ≤ 2*(∫ t in Ioo a b, θ t*deriv P t)) :
    (∫ t in closedBall c r, E t) ≤ 2*(P (c+r)-P (c-r)) := by
  obtain ⟨V,hV,he⟩ := hP.extend_real
  have hsub : closedBall c r ⊆ Ioo a b := by
    intro t ht
    have hh := abs_le.mp (show |t-c| ≤ r from by simpa only [mem_closedBall,Real.dist_eq] using ht)
    exact ⟨by linarith,by linarith⟩
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : deriv V t = deriv P t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (he hs).symm
  have hAC : AbsolutelyContinuousOnInterval V a b := hV.lipschitzOnWith.absolutelyContinuousOnInterval
  have hiD : IntegrableOn (deriv P) (Ioo a b) :=
    (hAC.intervalIntegrable_deriv.1.mono_set Ioo_subset_Ioc_self).congr
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht; exact hd t ht)
  have hiF : IntegrableOn (fun t => 2*deriv P t-E t) (Ioo a b) := (hiD.const_mul 2).sub hE
  have hpositive : 0 ≤ ∫ t in closedBall c r, 2*deriv P t-E t := by
    apply integral_closedBall_nonneg_of_smooth_tests hr ha hb _ hiF
    intro θ hθ hθc hθs hθ0
    obtain ⟨B,hB⟩ := hθc.exists_bound_of_continuous hθ.continuous
    have hiDE : IntegrableOn (fun t => θ t*deriv P t) (Ioo a b) :=
      hiD.bdd_mul hθ.continuous.aestronglyMeasurable (Eventually.of_forall hB)
    have hiEE : IntegrableOn (fun t => θ t*E t) (Ioo a b) :=
      hE.bdd_mul hθ.continuous.aestronglyMeasurable (Eventually.of_forall hB)
    have heI : (∫ t in Ioo a b, θ t*(2*deriv P t-E t)) =
        2*(∫ t in Ioo a b, θ t*deriv P t) - (∫ t in Ioo a b, θ t*E t) := by
      calc
        _ = ∫ t in Ioo a b, 2*(θ t*deriv P t)-θ t*E t := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by ring
        _ = _ := by
          rw [integral_sub (hiDE.const_mul 2) hiEE,integral_const_mul]
    rw [heI]
    exact sub_nonneg.mpr (htest θ hθ hθc hθs hθ0)
  have heF : (∫ t in closedBall c r, 2*deriv P t-E t) =
      2*(∫ t in closedBall c r, deriv P t) - (∫ t in closedBall c r, E t) := by
    rw [integral_sub ((hiD.mono_set hsub).const_mul 2) (hE.mono_set hsub),integral_const_mul]
  have hVI := (show AbsolutelyContinuousOnInterval V (c-r) (c+r) from
    hV.lipschitzOnWith.absolutelyContinuousOnInterval).integral_deriv_eq_sub
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc,
    ← Real.closedBall_eq_Icc] at hVI
  have heD : (∫ t in closedBall c r, deriv P t) = P (c+r)-P (c-r) := by
    calc
      _ = ∫ t in closedBall c r, deriv V t := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro t ht
        exact (hd t (hsub ht)).symm
      _ = _ := by
        rw [hVI,← he (by constructor <;> linarith : c+r ∈ Ioo a b),
          ← he (by constructor <;> linarith : c-r ∈ Ioo a b)]
  rw [heF,heD] at hpositive
  linarith

end RegularPointCoordinates

end

end OAI
