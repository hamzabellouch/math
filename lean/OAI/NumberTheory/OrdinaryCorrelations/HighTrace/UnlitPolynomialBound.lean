import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessBasicScales
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedUnlitTotalEqFixed

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
namespace NumericalLine

lemma unlit_polynomial_bound (S : PrimeSystem) (M ℓ L J t : ℕ) :
    unlitPrefactor S ℓ J ≤ witnessEntropyBase S M ℓ L J t ^ witnessEntropyDegree M ℓ L J t := by
  let Q := witnessEntropyBase S M ℓ L J t
  let N := ℓ*J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  have hH : 1 ≤ H := le_max_left _ _
  have hA := A_pos
  have hM := Nat.cast_nonneg (α:=ℝ) M
  have hℓ := Nat.cast_nonneg (α:=ℝ) ℓ
  have hL := Nat.cast_nonneg (α:=ℝ) L
  have ht := Nat.cast_nonneg (α:=ℝ) t
  have hN : N ≤ witnessSlotCount ℓ L J t := by
    simp only [N,witnessSlotCount,WitnessConfiguration.codeSlot_card]
    omega
  have hNcast : (N:ℝ) ≤ (witnessSlotCount ℓ L J t:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) ≤ N := by positivity
  have hslot := Nat.cast_nonneg (α:=ℝ) (witnessSlotCount ℓ L J t)
  have hQ : 2 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H] at *; linarith
  have hQA : A ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H] at *; linarith
  have hQℓ : (ℓ:ℝ)+2 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H] at *; linarith
  have hQN : (N:ℝ)+1 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H] at *; linarith
  have hQH : H ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H] at *; linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hHid : max 1 (∑ p : S.Index,(p:ℝ)⁻¹)=H := by
    exact congrArg (max (1:ℝ)) (sum_coe_sort S.primes (fun p : ℕ => (p:ℝ)⁻¹))
  unfold unlitPrefactor lineMassBound
  rw [hHid,←Nat.cast_mul]
  change A^N*((ℓ:ℝ)+2)^N*(2^ℓ*((N:ℝ)+1)*((N:ℝ)+1)^N*H^N) ≤ _
  calc
    _ ≤ Q^N*Q^N*(Q^ℓ*Q*Q^N*Q^N) := by gcongr
    _ = Q^(4*N+ℓ+1) := by simp only [pow_add,pow_mul,pow_one]; ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith)
      (by unfold witnessEntropyDegree; omega)

lemma source_unlit_prefactor_small (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      unlitPrefactor (sourceSystem B) (sourceLength B) ⌈C₀*Real.log B⌉₊ ≤
        Real.exp (B^(1+epsilon/2)) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num [epsilon] : 0 < epsilon/4)).tendsto_div_nhds_zero
  filter_upwards [source_witness_entropy_scales C₀ hC₀,
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_ge_atTop (1:ℝ)] with B hs hlog hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hbase0 : 0 ≤ witnessEntropyBase (sourceSystem B) (sourceListSlotBudget C₀ B)
      (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B) := by
    unfold witnessEntropyBase
    have := A_pos
    positivity
  apply (unlit_polynomial_bound (sourceSystem B) (sourceListSlotBudget C₀ B)
    (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B)).trans
  apply (pow_le_pow_left₀ hbase0 hs.2 _).trans
  rw [←Real.rpow_natCast,Real.rpow_def_of_pos (sq_pos_of_pos hB0),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hlog0 := Real.log_nonneg hB
  have hl := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (epsilon/4))).mp hlog
  have hd := mul_le_mul hs.1 hl hlog0 (Real.rpow_nonneg hB0.le _)
  have hid : B^(1+epsilon/4)*((1/2)*B^(epsilon/4)) = (1/2)*B^(1+epsilon/2) := by
    rw [mul_left_comm,←Real.rpow_add hB0]
    congr 2
    ring
  rw [hid] at hd
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem source_unlit_tail_small (h : ℕ) (τ T C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      unlitTailSum D h (sourceLength B) (pathLength B) cut (listCutoff B) ≤
        Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_unlit_prefactor_small C₀ hC₀,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+3*epsilon) 4 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hdom hB
  intro D cut
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let z := Real.exp ((1/2)*B^(1-epsilon))
  have hz : 1 ≤ z := Real.one_le_exp (by positivity)
  have hzp : ∀ p : (sourceSystem B).Index, z^2 ≤ (p:ℝ) := by
    intro p
    have he : z^2=sourceMinPrime B := by
      dsimp [z,sourceMinPrime]
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact (source_prime_lower B hB p).le
  have hh := unlit_tail_sum_bound (h:=h) (ℓ:=sourceLength B) (L:=pathLength B) D cut z hz hzp (listCutoff B)
  have hzt : 0 < z^(listCutoff B) := pow_pos (Real.exp_pos _) _
  have ht : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hs : (1/2)*B^(1+3*epsilon) ≤ (listCutoff B:ℝ)*((1/2)*B^(1-epsilon)) := by
    have hm := mul_le_mul_of_nonneg_right ht (show 0 ≤ (1/2)*B^(1-epsilon) by positivity)
    have he : B^(4*epsilon)*((1/2)*B^(1-epsilon))=(1/2)*B^(1+3*epsilon) := by
      rw [mul_left_comm,←Real.rpow_add hB0]
      congr 2
      ring
    rwa [he] at hm
  apply (le_div_iff₀ hzt).mpr (hh.trans hpref) |>.trans
  change Real.exp (B^(1+epsilon/2))/(Real.exp ((1/2)*B^(1-epsilon)))^(listCutoff B) ≤ _
  rw [←Real.exp_nat_mul,←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

end NumericalLine
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
