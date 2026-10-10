import Mathlib
import OAI.Geometry.PrescribedRicci.LpPowerBounds
import OAI.Geometry.PrescribedRicci.PowerIntegration

namespace OAI

/-! Directional Interpolation. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma directional_lp_interpolation {p : ℝ} (hp : 2 < p)
    (α β r s : ℝ≥0∞) [ENNReal.HolderTriple α β s] [ENNReal.HolderTriple s r 1]
    (hr : r * ENNReal.ofReal (p-2) = ENNReal.ofReal p)
    (v : E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (lpNorm (dir v f) (ENNReal.ofReal p) volume)^2 ≤
      (p-1)*lpNorm f α volume*lpNorm (dir v (dir v f)) β volume := by
  let a := dir v f
  let b := dir v a
  have ha : ContDiff ℝ ∞ a := dir_smooth v hf
  have hb : ContDiff ℝ ∞ b := dir_smooth v ha
  have hac : HasCompactSupport a := dir_compact v hc
  have hbc : HasCompactSupport b := dir_compact v hac
  have hfa : MemLp f α := hf.continuous.memLp_of_hasCompactSupport hc
  have hbb : MemLp b β := hb.continuous.memLp_of_hasCompactSupport hbc
  have hfb : MemLp (fun x => f x*b x) s := hfa.fun_mul hbb
  have hpc : Continuous (fun x => |a x|^(p-2)) :=
    ha.continuous.abs.rpow_const (fun _ => Or.inr (by linarith))
  have hps : HasCompactSupport (fun x => |a x|^(p-2)) :=
    hac.comp_left (g:=fun x : ℝ => |x|^(p-2)) (by simp [Real.zero_rpow (by linarith : p-2 ≠ 0)])
  have hpr : MemLp (fun x => |a x|^(p-2)) r := hpc.memLp_of_hasCompactSupport hps
  have hpw : lpNorm (fun x => |a x|^(p-2)) r volume =
      (lpNorm a (ENNReal.ofReal p) volume)^(p-2) := by
    simpa only [Real.norm_eq_abs,hr] using lpNorm_norm_rpow a ha.continuous.aestronglyMeasurable r (by linarith : 0 < p-2)
  have hI : |∫ x, f x*|a x|^(p-2)*b x| ≤
      (lpNorm f α volume*lpNorm b β volume)*(lpNorm a (ENNReal.ofReal p) volume)^(p-2) := by
    have he : (fun x => f x*|a x|^(p-2)*b x) = (fun x => (f x*b x)*|a x|^(p-2)) := by
      funext x; ring
    rw [he]
    calc
      _ ≤ lpNorm (fun x => (f x*b x)*|a x|^(p-2)) 1 volume :=
        integral_norm_le_lpNorm (hfb.aestronglyMeasurable.mul hpr.aestronglyMeasurable)
      _ ≤ lpNorm (fun x => f x*b x) s volume * lpNorm (fun x => |a x|^(p-2)) r volume := lpNorm_mul_le hfb hpr
      _ ≤ (lpNorm f α volume*lpNorm b β volume)*lpNorm (fun x => |a x|^(p-2)) r volume :=
        mul_le_mul_of_nonneg_right (lpNorm_mul_le hfa hbb) lpNorm_nonneg
      _ = _ := by rw [hpw]
  let Y := lpNorm a (ENNReal.ofReal p) volume
  have hY : 0 ≤ Y := lpNorm_nonneg
  have he := power_dir_integration hp v hf hc
  have hpow : Y^p ≤ ((p-1)*lpNorm f α volume*lpNorm b β volume)*Y^(p-2) := by
    calc
      Y^p = ∫ x, |a x|^p := by simpa [Y,Real.norm_eq_abs] using lpNorm_rpow_integral a ha.continuous.aestronglyMeasurable (by linarith : 0 < p)
      _ = -(p-1) * ∫ x, f x*|a x|^(p-2)*b x := he
      _ ≤ (p-1)*|∫ x, f x*|a x|^(p-2)*b x| := by
        nlinarith [neg_le_abs (∫ x, f x*|a x|^(p-2)*b x)]
      _ ≤ (p-1)*((lpNorm f α volume*lpNorm b β volume)*Y^(p-2)) :=
        mul_le_mul_of_nonneg_left hI (by linarith)
      _ = _ := by ring
  by_cases hz : Y = 0
  · change Y^2 ≤ _
    rw [hz,zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg (by linarith) lpNorm_nonneg) lpNorm_nonneg
  · have hYp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hz)
    have hyr : Y^p = Y^2*Y^(p-2) := by
      rw [← Real.rpow_natCast Y 2,← Real.rpow_add hYp]
      congr 1
      ring
    rw [hyr] at hpow
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hYp (p-2))).mp hpow
end TameInterpolation

end
end

end OAI
