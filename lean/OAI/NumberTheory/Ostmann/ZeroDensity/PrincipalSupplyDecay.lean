import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothing
import OAI.NumberTheory.Ostmann.ZeroDensity.RemainderDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyPrimeScales

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Ostmann.ZeroDensity

theorem supplyPrimeSample_tendsto :
    Tendsto (fun L : ℝ => (supplyPrimeSample L : ℝ)) atTop atTop := by
  have hr : Tendsto (fun L : ℝ => (Ostmann.Supply.supplyRadius L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Ostmann.Supply.supplyRadius_tendsto
  simpa only [supplyPrimeSample,Nat.cast_pow,Function.comp_def] using
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hr

theorem eventually_principal_supply_decay {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ‖smoothError (1 : DirichletCharacter ℂ 1) φ (supplyPrimeSample L : ℝ)‖ ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  obtain ⟨c,C,hc,hC,hmain⟩ := principal_smoothError_bound hφ hcompact hs
  have hlin := eventually_linear_mul_exp_le (a := 0) (b := (1 : ℝ)/2)
    (by norm_num) ((D+1)/c)
  have hconst := eventually_constant_exp_decay hC D
  filter_upwards [supplyPrimeSample_tendsto.eventually hmain,hlin,hconst] with L hm hl hCdec
  simp only [zero_mul,Real.exp_zero,mul_one] at hl
  have hroot : Real.exp ((1 : ℝ)/2*L) ≤ Real.sqrt (Real.log (supplyPrimeSample L : ℝ)) := by
    have hh := Real.sqrt_le_sqrt (log_supplyPrimeSample_lower L)
    have he : Real.sqrt (Real.exp L) = Real.exp ((1 : ℝ)/2*L) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring
    rwa [he] at hh
  have hlin' : (D+1)*L ≤ c*Real.sqrt (Real.log (supplyPrimeSample L : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (hl.trans hroot) hc.le
    have he : c*((D+1)/c*L) = (D+1)*L := by field_simp
    rwa [he] at hh
  calc
    _ ≤ C*(supplyPrimeSample L : ℝ)*Real.exp (-c*Real.sqrt (Real.log (supplyPrimeSample L : ℝ))) := hm
    _ ≤ C*(supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      positivity
    _ = (supplyPrimeSample L : ℝ)*(C*Real.exp (-(D+1)*L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hCdec (Nat.cast_nonneg _)

end Ostmann.ZeroDensity

end

end OAI
