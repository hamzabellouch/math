import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePivotFactor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalBudget

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

lemma source_pivot_absorb (τ : ℝ) :
    ∀ᶠ B : ℝ in atTop, sourcePivotFactor τ B ≤ B^(-(1-2*eta)) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num [eta,epsilon] : 0 < eta)).eventually_ge_atTop
    ((Real.log 4+1)*τ), eventually_gt_atTop (0:ℝ)] with B h hB
  unfold sourcePivotFactor
  calc
    _ ≤ B^eta/B^(1-eta) := div_le_div_of_nonneg_right h (Real.rpow_nonneg hB.le _)
    _ = _ := by rw [← Real.rpow_sub hB]; congr 1; ring

lemma source_lost_pivots : ∀ᶠ B : ℝ in atTop,
    B^((exceptionalBudget B:ℕ):ℝ) ≤ Real.exp B := by
  have ht := (isLittleO_log_rpow_atTop (by norm_num [rho] : 0 < rho/2)).tendsto_div_nhds_zero
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_ge_atTop (1:ℝ)] with B h hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hN := ceil_rpow_le_two B (1-rho/2) hB (by norm_num [rho])
  change (exceptionalBudget B:ℝ) ≤ 2*B^(1-rho/2) at hN
  rw [Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_nonneg hB
  have hlogB := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (rho/2))).mp h
  have hmul := mul_le_mul_of_nonneg_left hlogB (Real.rpow_nonneg hB0.le (1-rho/2))
  have he : B^(1-rho/2)*((1/2)*B^(rho/2)) = B/2 := by
    rw [mul_left_comm,← Real.rpow_add hB0]
    rw [show (1-rho/2)+rho/2=1 by ring,Real.rpow_one]
    ring
  rw [he] at hmul
  have hbound := mul_le_mul_of_nonneg_right hN hlog
  nlinarith

lemma truncated_pivot_power (B K a : ℝ) (g N : ℕ) (hB : 1 ≤ B)
    (hK : 0 ≤ K) (hKa : K ≤ B^(-a)) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hN : B^(N:ℝ) ≤ Real.exp B) :
    K^(g-N) ≤ Real.exp B * B^(-a*(g:ℝ)) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hcast : (g:ℝ) ≤ ((g-N:ℕ):ℝ)+(N:ℝ) := by exact_mod_cast (show g ≤ g-N+N by omega)
  have hg : -a*((g-N:ℕ):ℝ) ≤ -a*(g:ℝ)+a*(N:ℝ) := by nlinarith
  have hb : B^(a*(N:ℝ)) ≤ Real.exp B :=
    (Real.rpow_le_rpow_of_exponent_le hB (by nlinarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N])).trans hN
  calc
    _ ≤ (B^(-a))^(g-N) := pow_le_pow_left₀ hK hKa _
    _ = B^(-a*((g-N:ℕ):ℝ)) := by rw [Real.rpow_mul hB0.le,Real.rpow_natCast]
    _ ≤ B^(-a*(g:ℝ)+a*(N:ℝ)) := Real.rpow_le_rpow_of_exponent_le hB hg
    _ = B^(-a*(g:ℝ))*B^(a*(N:ℝ)) := Real.rpow_add hB0 ..
    _ ≤ B^(-a*(g:ℝ))*Real.exp B := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hB0.le _)
    _ = _ := mul_comm ..

theorem source_record_fiber_bound (τ T C₀ : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (h : ℕ) (w₀ : ClosedLine h (sourceLength B)) (hh : 0 < h) (r : ℕ)
      (hr₀ : (returnSteps w₀).card=r) (err : ℝ),
      (∑ x : RecordPacket D (pathLength B) w₀ hh r hr₀ (listCutoff B) (exceptionalBudget B),
        traceIntegrationMajorant x.line hh x.primitives x.record T err) ≤
        Real.exp (err+2*B) * B^(-100*(r:ℝ) - (1+8*eta)*((goodEdges w₀).card:ℝ) +
          epsilon*((badEdges w₀).card:ℝ)) := by
  filter_upwards [source_integrated_record_sum τ T hτ,source_pivot_absorb τ,source_lost_pivots,
    RecordPacket.source_entropy_sublinear C₀ 1 hC₀ (by norm_num),
    eventually_ge_atTop (1:ℝ)] with B hsum hK hN hent hB
  intro D h w₀ hh r hr₀ err
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hp := truncated_pivot_power B (sourcePivotFactor τ B) (1-2*eta)
    (goodEdges w₀).card (exceptionalBudget B) hB
    (sourcePivotFactor_pos τ B (zero_lt_one.trans_le hτ) hB0).le hK
    (by norm_num [eta,epsilon]) (by norm_num [eta,epsilon]) hN
  have hs := hsum C₀ D h (sourceLength B) (pathLength B) w₀ hh r hr₀
    (listCutoff B) (exceptionalBudget B) err
  apply hs.trans
  have hg := mul_le_mul hp hent
    (mul_nonneg (Nat.cast_nonneg _) (RecordPacket.exceptionalCost_nonneg ..))
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hB0.le _))
  have hm := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (Real.exp_pos err).le (Real.rpow_nonneg hB0.le (-100*(r:ℝ))))
  have ho := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hB0.le
    (-(epsilon/10)*((goodEdges w₀).card:ℝ)+epsilon*((badEdges w₀).card:ℝ)))
  have he : Real.exp err * B^(-100*(r:ℝ)) *
      ((Real.exp B * B^(-(1-2*eta)*((goodEdges w₀).card:ℝ))) * Real.exp (1*B)) *
        B^(-(epsilon/10)*((goodEdges w₀).card:ℝ)+epsilon*((badEdges w₀).card:ℝ)) =
      Real.exp (err+2*B) * B^(-100*(r:ℝ)-(1+8*eta)*((goodEdges w₀).card:ℝ)+
        epsilon*((badEdges w₀).card:ℝ)) := by
    rw [Real.rpow_def_of_pos hB0,Real.rpow_def_of_pos hB0,Real.rpow_def_of_pos hB0,
      Real.rpow_def_of_pos hB0]
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    norm_num [eta,epsilon]
    ring
  calc
    _ = _ := by ring
    _ ≤ _ := ho
    _ = _ := he

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
