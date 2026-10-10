import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaCompactStrip
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaStrip
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingAbel
import StrongPNT.Erdos970.PNT5_Strong

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

theorem principalCumulative_vonMangoldt_eq {t : ℝ} (ht : 0 ≤ t) :
    principalCumulative ArithmeticFunction.vonMangoldt t = ChebyshevPsi t := by
  unfold principalCumulative ChebyshevPsi
  rw [Nat.floor_add_one ht, Nat.range_succ_eq_Icc_zero]

theorem principal_cumulative_strong_PNT :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ t : ℝ in atTop,
      |principalCumulative ArithmeticFunction.vonMangoldt t-t| ≤
        K*t*Real.exp (-c*Real.sqrt (Real.log t)) := by
  obtain ⟨c, hc, hPNT⟩ := Strong_PNT
  obtain ⟨K, hK, hbound⟩ := hPNT.exists_pos
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [hbound.bound, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  change ‖ChebyshevPsi t-t‖ ≤ K*‖t*Real.exp (-c*(Real.log t)^(1/2 : ℝ))‖ at ht
  rw [principalCumulative_vonMangoldt_eq ht0]
  simp only [Real.norm_eq_abs] at ht
  rw [abs_of_nonneg (by positivity : 0 ≤ t*Real.exp (-c*(Real.log t)^(1/2 : ℝ))),
    ← Real.sqrt_eq_rpow] at ht
  nlinarith [ht]

theorem half_sqrt_log_le_sqrt_log {X t : ℝ} (hX : 4 ≤ X) (ht : X/2 ≤ t) :
    Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log t) := by
  have hXpos : 0 < X := by linarith
  have htpos : 0 < t := by linarith
  have hlog4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hX
  have hlogt := Real.log_le_log (by positivity : 0 < X/2) ht
  rw [Real.log_div hXpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogt
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ)^2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [hlog4eq] at hlog4
  have hXlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have htlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hXs := Real.sq_sqrt hXlog
  have hts := Real.sq_sqrt htlog
  have hXr := Real.sqrt_nonneg (Real.log X)
  have htr := Real.sqrt_nonneg (Real.log t)
  nlinarith

theorem principal_cumulative_uniform_PNT :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (X/2) X,
        |principalCumulative ArithmeticFunction.vonMangoldt t-t| ≤
          K*X*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c, K, hc, hK, h⟩ := principal_cumulative_strong_PNT
  obtain ⟨T, hT⟩ := eventually_atTop.1 h
  refine ⟨c/2, K, by positivity, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max (2*T) (4 : ℝ))] with X hX
  intro t ht
  have hX4 : 4 ≤ X := (le_max_right _ _).trans hX
  have htT : T ≤ t := by have := (le_max_left (2*T) (4 : ℝ)).trans hX; linarith [ht.1]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hr := half_sqrt_log_le_sqrt_log hX4 ht.1
  have he : Real.exp (-c*Real.sqrt (Real.log t)) ≤
      Real.exp (-(c/2)*Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ K*t*Real.exp (-c*Real.sqrt (Real.log t)) := hT t htT
    _ ≤ K*X*Real.exp (-(c/2)*Real.sqrt (Real.log X)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left ht.2 hK.le) he
        (Real.exp_nonneg _) (mul_nonneg hK.le (by linarith))

end Ostmann.ZeroDensity

end

end OAI
