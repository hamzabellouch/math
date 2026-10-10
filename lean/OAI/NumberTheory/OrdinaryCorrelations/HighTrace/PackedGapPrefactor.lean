import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EventuallyConstPowLeExp
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapSum

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
namespace NumericalLine

noncomputable def packedGapPrefactor (S : PrimeSystem) (ℓ L J t : ℕ) : ℝ :=
  (A^(ℓ*J)*((ℓ:ℝ)+2)^(ℓ*J))*(gapTemplateBudget ℓ L J t:ℝ)*
    (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(ℓ*J)

lemma packed_gap_polynomial_bound (S : PrimeSystem) (M ℓ L J t : ℕ) :
    packedGapPrefactor S ℓ L J t ≤ witnessEntropyBase S M ℓ L J t ^ witnessEntropyDegree M ℓ L J t := by
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
  have hpath : 2*(ℓ:ℝ)+1 ≤ Q^2 := by nlinarith [sq_nonneg (Q-(ℓ:ℝ)-2),sq_nonneg (ℓ:ℝ)]
  unfold packedGapPrefactor gapTemplateBudget
  change (A^N*((ℓ:ℝ)+2)^N)*(((N+1)*2^ℓ*(N+1)^N*(2*ℓ+1)^(L*t)*(N+1)^(2*t):ℕ):ℝ)*H^N ≤ _
  push_cast
  calc
    _ ≤ (Q^N*Q^N)*(Q*Q^ℓ*Q^N*(Q^2)^(L*t)*Q^(2*t))*Q^N := by gcongr
    _ = Q^(4*N+ℓ+1+2*(L*t)+2*t) := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith)
      (by unfold witnessEntropyDegree; dsimp only [N] at hN ⊢; nlinarith [hN])

lemma source_packed_gap_prefactor_small (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      packedGapPrefactor (sourceSystem B) (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B) ≤
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
  apply (packed_gap_polynomial_bound (sourceSystem B) (sourceListSlotBudget C₀ B)
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

theorem source_packed_gap_small (h : ℕ) (hh : 0 < h) (τ T C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      packedGapSum D h (sourceLength B) (pathLength B) (listCutoff B) cut ≤
        Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_packed_gap_prefactor_small C₀ hC₀,
    source_witness_delta_saving C₀ h hC₀,source_eventually_large h,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+3*epsilon) 4 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hdelta hlarge hdom hB
  intro D cut
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hnd : ∀ p : (sourceSystem B).Index,¬(p:ℕ) ∣ h := by
    intro p hd
    exact (not_le_of_gt (hlarge.2 p).2) (Nat.le_of_dvd hh hd)
  have hb := packedGapSum_bound (D:=D) (h:=h) (ℓ:=sourceLength B) (L:=pathLength B) (t:=listCutoff B)
    cut (sourceMinPrime B) B hP hB0.le
    (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩) hnd
  have hδ : (2+B)/sourceMinPrime B ≤ Real.exp (-(1/2)*B^(1-epsilon)) :=
    (le_max_right _ _).trans hdelta
  have ht : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hs : (1/2)*B^(1+3*epsilon) ≤ (listCutoff B:ℝ)*((1/2)*B^(1-epsilon)) := by
    have hm := mul_le_mul_of_nonneg_right ht (show 0 ≤ (1/2)*B^(1-epsilon) by positivity)
    have he : B^(4*epsilon)*((1/2)*B^(1-epsilon))=(1/2)*B^(1+3*epsilon) := by
      rw [mul_left_comm,←Real.rpow_add hB0]
      congr 2
      ring
    rwa [he] at hm
  apply hb.trans
  rw [←mul_assoc,←mul_assoc]
  change packedGapPrefactor (sourceSystem B) (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B)*
    ((2+B)/sourceMinPrime B)^(listCutoff B) ≤ _
  apply (mul_le_mul hpref (pow_le_pow_left₀ (by positivity) hδ _) (by positivity) (Real.exp_pos _).le).trans
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end NumericalLine
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
