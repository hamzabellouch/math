import OAI.MeasureTheory.Falconer.Radial.AffinePlaneCover
import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # The Frostman power bound near a lower-dimensional affine plane -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {k d : ℕ}

theorem affine_plane_frostman_bound (μ : Measure (Space d))
    (F : Space k →ₗᵢ[ℝ] Space d) (a : Space d) {M A s C r : ℝ}
    (hM : 0 ≤ M) (hA : ‖a‖ ≤ A) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    μ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(2*(M+A+1)+1)^k)*r^(s-(k:ℝ))) := by
  classical
  have hA0 : 0 ≤ A := (norm_nonneg a).trans hA
  obtain ⟨S,hcard,hcover⟩ := affine_plane_neighborhood_cover F a hM hA hr hr1
  have hmono : ∀ᵐ x ∂μ, x ∈ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} →
      x ∈ ⋃ c ∈ S, ball c (3*r) := by
    filter_upwards [hbounded] with x hx
    intro hnear
    obtain ⟨c,hc,hxc⟩ := hcover x hx hnear
    exact mem_iUnion₂.mpr ⟨c,hc,hxc⟩
  have hcard' : (S.card:ℝ) ≤ ((2*(M+A+1)+1)/r)^k := by
    apply hcard.trans
    apply pow_le_pow_left₀ (by positivity)
    have he : 2*(M+A+1)/r+1 = (2*(M+A+1)+r)/r := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith only [hr1]) hr.le
  have hmass : μ {x | ∃ y : Space k, ‖x-(a+F y)‖ ≤ r} ≤
      ENNReal.ofReal ((S.card:ℝ)*(C*(3*r)^s)) := by
    apply (measure_mono_ae hmono).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc
      _ ≤ ∑ c ∈ S, ENNReal.ofReal (C*(3*r)^s) :=
        Finset.sum_le_sum (fun c _ => hfrost c (3*r) (by positivity))
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg S.card),ENNReal.ofReal_natCast]
  apply hmass.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (((2*(M+A+1)+1)/r)^k)*(C*(3*r)^s) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le,div_pow,Real.rpow_sub hr,
        Real.rpow_natCast]
      field_simp

end Falconer

end OAI
