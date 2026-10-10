import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RootNotDestination
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePivotAbsorb

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

lemma sourceLength_ge (B : ℝ) (hB : 2 ≤ B) : B ≤ (sourceLength B:ℝ) := by
  have hf := Nat.lt_floor_add_one B
  simp only [sourceLength,Nat.cast_mul,Nat.cast_ofNat]
  linarith

lemma source_numeric_margin (g b r l : ℝ) (hl : l=g+b+r)
    (hb : b ≤ 10*(r+1)) (hr : 0 ≤ r) (hlg : 10000000 ≤ l) :
    -98*r-(1+8*eta)*g+epsilon*b+eta*l ≤ -(1+4*eta)*l := by
  norm_num [eta,epsilon] at *
  linarith

lemma source_topology_prefactor : ∀ᶠ B : ℝ in atTop,
    ((sourceLength B:ℝ)+1) ≤ B^2 ∧
    Real.exp (1+2*B)*(4:ℝ)^(sourceLength B) ≤ B^(eta*(sourceLength B:ℝ)) := by
  have heta : 0 < eta := by norm_num [eta,epsilon]
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((3+Real.log 4)/eta),
    eventually_ge_atTop (3:ℝ)] with B hlog hB
  have hB0 : 0 < B := by linarith
  have hℓ := sourceLength_le B hB0.le
  have hℓ' := sourceLength_ge B (by linarith)
  refine ⟨by nlinarith,?_⟩
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<4),
    ← Real.exp_add,Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  have hlog' := (div_le_iff₀ heta).mp hlog
  have hmul := mul_le_mul_of_nonneg_right hlog' (Nat.cast_nonneg (sourceLength B))
  nlinarith

theorem source_topology_margin : ∀ᶠ B : ℝ in atTop,
    ∀ (g b r : ℕ), sourceLength B=g+b+r → b ≤ 10*(r+1) →
      (4:ℝ)^(sourceLength B)*((sourceLength B:ℝ)+1)^r *
        (Real.exp (1+2*B)*B^(-100*(r:ℝ)-(1+8*eta)*(g:ℝ)+epsilon*(b:ℝ))) ≤
          B^(-(1+4*eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_topology_prefactor,eventually_ge_atTop (10000000:ℝ)] with B hs hB
  intro g b r he hb
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hℓ := sourceLength_ge B (by linarith)
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (sourceLength B:ℝ)+1) hs.1 r
  have hrpow : ((sourceLength B:ℝ)+1)^r ≤ B^(2*(r:ℝ)) := by
    rw [Real.rpow_mul hB0.le,Real.rpow_natCast,Real.rpow_two]
    exact hh
  have hle := mul_le_mul hs.2 hrpow (pow_nonneg (by positivity) r)
    (Real.rpow_nonneg hB0.le (eta*(sourceLength B:ℝ)))
  have hd : -100*(r:ℝ)-(1+8*eta)*(g:ℝ)+epsilon*(b:ℝ)+eta*(sourceLength B:ℝ)+2*(r:ℝ) ≤
      -(1+4*eta)*(sourceLength B:ℝ) := by
    have hl : (sourceLength B:ℝ)=(g:ℝ)+(b:ℝ)+(r:ℝ) := by exact_mod_cast he
    have hb' : (b:ℝ) ≤ 10*((r:ℝ)+1) := by exact_mod_cast hb
    have hm := source_numeric_margin (g:ℝ) (b:ℝ) (r:ℝ) (sourceLength B:ℝ)
      hl hb' (Nat.cast_nonneg r) (hB.trans hℓ)
    linarith
  have ho := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hB0.le
    (-100*(r:ℝ)-(1+8*eta)*(g:ℝ)+epsilon*(b:ℝ)))
  calc
    _ = _ := by ring
    _ ≤ _ := ho
    _ = B^(-100*(r:ℝ)-(1+8*eta)*(g:ℝ)+epsilon*(b:ℝ)+eta*(sourceLength B:ℝ)+2*(r:ℝ)) := by
      rw [← Real.rpow_add hB0,← Real.rpow_add hB0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 hd

theorem source_topology_fiber_bound (τ T C₀ : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (h : ℕ) (w₀ : ClosedLine h (sourceLength B)) (hh : 0 < h) (r : ℕ)
      (hr₀ : (returnSteps w₀).card=r) (err : ℝ), err ≤ 1 →
      (4:ℝ)^(sourceLength B)*((sourceLength B:ℝ)+1)^r *
        (∑ x : RecordPacket D (pathLength B) w₀ hh r hr₀ (listCutoff B) (exceptionalBudget B),
          traceIntegrationMajorant x.line hh x.primitives x.record T err) ≤
          B^(-(1+4*eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_record_fiber_bound τ T C₀ hτ hC₀,source_topology_margin,
    eventually_ge_atTop (1:ℝ)] with B hs hm hB
  intro D h w₀ hh r hr₀ err herr
  have hh' := hs D h w₀ hh r hr₀ err
  have he : Real.exp (err+2*B) ≤ Real.exp (1+2*B) := Real.exp_le_exp.mpr (by linarith)
  have hpower := Real.rpow_nonneg (zero_le_one.trans hB)
    (-100*(r:ℝ)-(1+8*eta)*((goodEdges w₀).card:ℝ)+epsilon*((badEdges w₀).card:ℝ))
  have hf := hh'.trans (mul_le_mul_of_nonneg_right he hpower)
  have hcount : 0 ≤ (4:ℝ)^(sourceLength B)*((sourceLength B:ℝ)+1)^r := by positivity
  apply (mul_le_mul_of_nonneg_left hf hcount).trans
  apply hm (goodEdges w₀).card (badEdges w₀).card r
  · simpa only [hr₀] using (length_good_bad_return w₀).symm
  · simpa only [hr₀] using bad_edges_le w₀

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
