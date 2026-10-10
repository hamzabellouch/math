import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatMoments

namespace OAI

/-! A uniform height-power bound for the full nonzero heat-mode mass. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaHeatPowerConstant (s : ℂ) (k : ℕ) : ℝ :=
  ((k.factorial:ℝ)/(4*Real.pi^2/27)^k)*Real.Gamma (s.re+(k:ℝ)-1)

lemma cubicThetaHeatPowerConstant_nonneg {s : ℂ} {k : ℕ}
    (hk : 0<s.re+(k:ℝ)-1) : 0 ≤ cubicThetaHeatPowerConstant s k := by
  unfold cubicThetaHeatPowerConstant
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))
    (Real.Gamma_pos_of_pos hk).le

lemma cubicThetaNonzeroHeat_height_bound {v : ℝ} (hv : 0<v) (s : ℂ) (k : ℕ)
    (hk : 0<s.re+(k:ℝ)-1) (h : Eisenstein) :
    (if h=0 then 0 else ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) ≤
      (cubicThetaHeatPowerConstant s k*v^(-2*(s.re+(k:ℝ)-1)))*(norm h)^(-(k:ℝ)) := by
  by_cases hh : h=0
  · rw [ite_eq_left hh]
    exact mul_nonneg (mul_nonneg (cubicThetaHeatPowerConstant_nonneg hk)
      (Real.rpow_nonneg hv.le _)) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [ite_eq_right hh]
    apply (cubicThetaNonzeroHeat_norm_mass_power hv (cubicThetaRowHeatScale_pos hh) s k hk).trans_eq
    have he : (v^2)^(-(s.re+(k:ℝ)-1))=v^(-2*(s.re+(k:ℝ)-1)) := by
      rw [←Real.rpow_natCast_mul hv.le]
      congr 1
      push_cast
      ring
    rw [cubicThetaRowHeatScale_eq,mul_pow,he,
      Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
    unfold cubicThetaHeatPowerConstant
    ring

theorem cubicThetaNonzeroHeat_mass_height_bound {v : ℝ} (hv : 0<v) (s : ℂ)
    (k : ℕ) (hk : 1<(k:ℝ)) (hks : 0<s.re+(k:ℝ)-1) :
    (∑' h : Eisenstein, if h=0 then 0 else
      ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) ≤
      (cubicThetaHeatPowerConstant s k*(∑' h : Eisenstein, (norm h)^(-(k:ℝ))))*
        v^(-2*(s.re+(k:ℝ)-1)) := by
  calc
    _ ≤ ∑' h : Eisenstein,
        (cubicThetaHeatPowerConstant s k*v^(-2*(s.re+(k:ℝ)-1)))*(norm h)^(-(k:ℝ)) :=
      Summable.tsum_le_tsum (cubicThetaNonzeroHeat_height_bound hv s k hks)
        (cubicThetaNonzeroHeat_mass_summable hv s)
        ((summable_eisenstein_norm_rpow hk).mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

end CubicFirstMoment

end

end OAI
