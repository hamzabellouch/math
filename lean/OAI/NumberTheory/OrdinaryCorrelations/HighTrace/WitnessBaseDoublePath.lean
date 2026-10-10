import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessBasicScales
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ComponentBoundAfterGap

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.NumericalSubtrees Finset Classical Filter
noncomputable section

lemma witness_base_double_path (S : PrimeSystem) (M ℓ L J t : ℕ) :
    witnessEntropyBase S M ℓ (L+L) J t ≤ 2*witnessEntropyBase S M ℓ L J t := by
  unfold witnessEntropyBase witnessSlotCount
  rw [WitnessConfiguration.codeSlot_card,WitnessConfiguration.codeSlot_card]
  push_cast
  have hH : 0 ≤ max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹) := le_trans (by norm_num) (le_max_left _ _)
  have hA := A_pos
  have hM := Nat.cast_nonneg (α:=ℝ) M
  have hℓ := Nat.cast_nonneg (α:=ℝ) ℓ
  have hL := Nat.cast_nonneg (α:=ℝ) L
  have hJ := Nat.cast_nonneg (α:=ℝ) J
  have ht := Nat.cast_nonneg (α:=ℝ) t
  nlinarith
lemma witness_degree_double_path (M ℓ L J t : ℕ) :
    witnessEntropyDegree M ℓ (L+L) J t ≤ 2*witnessEntropyDegree M ℓ L J t := by
  unfold witnessEntropyDegree witnessSlotCount
  rw [WitnessConfiguration.codeSlot_card,WitnessConfiguration.codeSlot_card]
  nlinarith

namespace NumericalLine
lemma source_double_path_prefactor (C₀ : ℝ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,
      packedGapPrefactor (sourceSystem B) (sourceLength B) (pathLength B+pathLength B)
        ⌈C₀*Real.log B⌉₊ (listCutoff B) ≤ Real.exp (B^(1+epsilon/2)) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num [epsilon] : 0<epsilon/4)).tendsto_div_nhds_zero
  filter_upwards [source_witness_entropy_scales C₀ hC₀,
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/6)),
    eventually_ge_atTop (2:ℝ)] with B hs hlog hB
  have hB1 : 1≤B := by linarith
  have hB0 : 0<B := by linarith
  let M := sourceListSlotBudget C₀ B
  let ℓ := sourceLength B
  let L := pathLength B
  let J := ⌈C₀*Real.log B⌉₊
  let t := listCutoff B
  have hbase0 : 0≤witnessEntropyBase (sourceSystem B) M ℓ (L+L) J t := by
    unfold witnessEntropyBase
    have := A_pos
    positivity
  have hbase : witnessEntropyBase (sourceSystem B) M ℓ (L+L) J t ≤ B^3 := by
    calc
      _ ≤ 2*witnessEntropyBase (sourceSystem B) M ℓ L J t := witness_base_double_path ..
      _ ≤ 2*(B^2) := mul_le_mul_of_nonneg_left hs.2 (by norm_num)
      _ ≤ B^3 := by nlinarith [sq_nonneg B]
  have hdegree : (witnessEntropyDegree M ℓ (L+L) J t:ℝ) ≤ 2*B^(1+epsilon/4) := by
    calc
      _ ≤ ((2*witnessEntropyDegree M ℓ L J t:ℕ):ℝ) := Nat.cast_le.mpr (witness_degree_double_path ..)
      _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_left hs.1 (by norm_num)
  apply (packed_gap_polynomial_bound (sourceSystem B) M ℓ (L+L) J t).trans
  apply (pow_le_pow_left₀ hbase0 hbase _).trans
  rw [←Real.rpow_natCast,Real.rpow_def_of_pos (pow_pos hB0 3),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hlog0 := Real.log_nonneg hB1
  have hl := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (epsilon/4))).mp hlog
  have hd := mul_le_mul hdegree hl hlog0 (by positivity : 0≤2*B^(1+epsilon/4))
  
  have hid' : (2*B^(1+epsilon/4))*((1/6)*B^(epsilon/4))=(1/3)*B^(1+epsilon/2) := by
    calc
      _ = (1/3)*(B^(1+epsilon/4)*B^(epsilon/4)) := by ring
      _ = _ := by rw [←Real.rpow_add hB0]; congr 2; ring
  rw [hid'] at hd
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

lemma source_disconnected_threshold (C₀ : ℝ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,
      (((((2*sourceLength B)/pathLength B+6*listCutoff B+1)^2)*
        ((2*⌈C₀*Real.log B⌉₊+1)*listCutoff B)^8:ℕ):ℝ) ≤ B^(1-2*rho) := by
  filter_upwards [source_component_budget,source_witness_basic_scales C₀ hC₀,
    eventually_const_mul_rpow_le (2*rho+8*(epsilon/8+4*epsilon)) (1-2*rho)
      (32^2*6^8) (by norm_num [rho,epsilon])] with B hcomp hs hdom
  obtain ⟨hB,hM,htL,ht,hJ,hH⟩ := hs
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have ht' := ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])
  have hJ1 : 1≤B^(epsilon/8) := Real.one_le_rpow hB (by norm_num [epsilon])
  have hn : (((2*⌈C₀*Real.log B⌉₊+1)*listCutoff B:ℕ):ℝ) ≤ 6*B^(epsilon/8+4*epsilon) := by
    push_cast
    calc
      _ ≤ (3*B^(epsilon/8))*(2*B^(4*epsilon)) := mul_le_mul (by linarith) ht' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [Real.rpow_add hB0]; ring
  have hq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) _) hcomp.2 2
  have hn8 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) _) hn 8
  have hmul := mul_le_mul hq hn8 (by positivity) (by positivity)
  have he : (32*B^rho)^2*(6*B^(epsilon/8+4*epsilon))^8 =
      (32^2*6^8)*B^(2*rho+8*(epsilon/8+4*epsilon)) := by
    have hp2 : (B^rho)^2 = B^(rho*2) := by
      rw [Real.rpow_mul hB0.le]
      norm_num
    have hp8 : (B^(epsilon/8+4*epsilon))^8 = B^((epsilon/8+4*epsilon)*8) := by
      rw [Real.rpow_mul hB0.le]
      norm_num
    rw [mul_pow,mul_pow,hp2,hp8]
    calc
      _ = (32^2*6^8)*(B^(rho*2)*B^((epsilon/8+4*epsilon)*8)) := by ring
      _ = _ := by rw [←Real.rpow_add hB0]; congr 2; ring
  rw [he] at hmul
  exact le_trans (by simpa only [Nat.cast_mul,Nat.cast_pow] using hmul) hdom

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
