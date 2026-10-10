import OAI.Analysis.LipschitzHilbert.Estimates.CountingDiscard
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The moving good-path exceptional set is charged to the original
sum. Its exp(-9L) area beats every fixed polynomial L2 loss. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem eventually_original_moving_exception (q m Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (X E : Type*) [MeasurableSpace X] [NormedAddCommGroup E],
    ∀ (μ : Measure X) (P : X → E), MemLp P 2 μ →
    ∀ (bad source testing : Set X), μ bad ≠ ∞ →
    ∀ N : ℝ, 0 ≤ N → μ.real source = N^2*μ.real testing → N ≤ Real.exp (2*L) →
      (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*μ.real source →
      μ.real bad ≤ L^m*μ.real source*Real.exp (-9*L) →
      IntegrableOn (fun x => ‖P x‖) bad μ ∧
        (∫ x in bad, ‖P x‖ ∂μ) ≤ L^(-Q)*N*μ.real testing := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q+m/2+Q) (5/2)
    (by norm_num : (0:ℝ) < 5/2)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  intro X E _ _ μ P hP bad source testing hbad N hN hratio hNexp hmodel harea
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hb := counting_discard_cost μ P hP hbad (Real.rpow_nonneg hL0.le q)
    (Real.rpow_nonneg hL0.le m) hN hratio hNexp hmodel harea
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hpower : L^(q+m/2+Q)*L^(-Q) = L^(q+m/2) := by
    rw [←Real.rpow_add hL0]
    congr 1
    ring
  have hdecay : L^(q+m/2)*Real.exp (-(5/2:ℝ)*L) ≤ L^(-Q) := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le (-Q))
    calc
      _ = (L^(q+m/2+Q)*Real.exp (-(5/2:ℝ)*L))*L^(-Q) := by
        rw [show L^(q+m/2+Q)*Real.exp (-(5/2:ℝ)*L)*L^(-Q) =
          (L^(q+m/2+Q)*L^(-Q))*Real.exp (-(5/2:ℝ)*L) by ring,hpower]
      _ ≤ 1*L^(-Q) := hh
      _ = _ := one_mul _
  have heq : (L^q*Real.sqrt (L^m))*Real.exp ((2-9/2)*L) =
      L^(q+m/2)*Real.exp (-(5/2:ℝ)*L) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hL0.le,←Real.rpow_add hL0]
    congr 2 <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdecay hN) measureReal_nonneg

end LipschitzHilbert

end

end OAI
