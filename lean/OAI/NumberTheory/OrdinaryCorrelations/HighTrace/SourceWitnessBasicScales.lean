import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessDelta
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessEntropyBase

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

lemma source_witness_basic_scales (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      1 ≤ B ∧ (sourceListSlotBudget C₀ B:ℝ) ≤ B ∧
      (listCutoff B:ℝ)*(pathLength B:ℝ) ≤ B ∧ (listCutoff B:ℝ) ≤ B ∧
      (⌈C₀*Real.log B⌉₊:ℝ) ≤ B^(epsilon/8) ∧
      max 1 (∑ p ∈ (sourceSystem B).primes,(p:ℝ)⁻¹) ≤ B := by
  filter_upwards [source_list_slots_power C₀ hC₀,
    eventually_const_mul_rpow_le (1-rho+4*epsilon+rho/8) 1 4 (by norm_num [rho,epsilon]),
    eventually_const_mul_rpow_le (4*epsilon+(1-rho)) 1 2 (by norm_num [rho,epsilon]),
    eventually_const_mul_rpow_le (4*epsilon) 1 2 (by norm_num [epsilon]),
    eventually_log_ceil_le C₀ (epsilon/8) hC₀ (by norm_num [epsilon]),
    RecordPacket.source_mass_le_log,eventually_ge_atTop (1:ℝ)] with B hM hM' htL ht hJ hmass hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have htc := ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])
  have hLc : (pathLength B:ℝ) ≤ B^(1-rho) := Nat.floor_le (Real.rpow_nonneg hB0.le _)
  refine ⟨hB,?_,?_,?_,hJ,?_⟩
  · simpa only [Real.rpow_one] using hM.trans hM'
  · calc
      _ ≤ (2*B^(4*epsilon))*B^(1-rho) := mul_le_mul htc hLc (Nat.cast_nonneg _) (by positivity)
      _ = 2*B^(4*epsilon+(1-rho)) := by rw [Real.rpow_add hB0]; ring
      _ ≤ B := by simpa only [Real.rpow_one] using htL
  · exact htc.trans (by simpa only [Real.rpow_one] using ht)
  · apply max_le hB
    have he : (∑ p ∈ (sourceSystem B).primes,(p:ℝ)⁻¹)=RecordPacket.codeEntropyMass (sourceSystem B) := by
      exact (sum_coe_sort _ _).symm
    rw [he]
    exact hmass.trans ((Real.log_le_sub_one_of_pos hB0).trans (by linarith))

lemma source_witness_entropy_scales (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      (witnessEntropyDegree (sourceListSlotBudget C₀ B) (sourceLength B)
        (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B):ℝ) ≤ B^(1+epsilon/4) ∧
      witnessEntropyBase (sourceSystem B) (sourceListSlotBudget C₀ B) (sourceLength B)
        (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B) ≤ B^2 := by
  filter_upwards [source_witness_basic_scales C₀ hC₀,
    eventually_const_mul_rpow_le (1+epsilon/8) (1+epsilon/4) 50 (by norm_num [epsilon]),
    eventually_const_mul_rpow_le (1+epsilon/8) 2 (A+14) (by norm_num [epsilon])] with B hs hd hb
  obtain ⟨hB,hM,htL,ht,hJ,hH⟩ := hs
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hℓ := sourceLength_le B hB0.le
  have hL := pathLength_le B hB
  let R := B^(1+epsilon/8)
  have hBR : B ≤ R := by
    conv_lhs => rw [←Real.rpow_one B]
    exact Real.rpow_le_rpow_of_exponent_le hB (by norm_num [epsilon])
  have hR1 : 1 ≤ R := hB.trans hBR
  have hℓJ : (sourceLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ) ≤ 2*R := by
    calc
      _ ≤ (2*B)*B^(epsilon/8) := mul_le_mul hℓ hJ (Nat.cast_nonneg _) (by positivity)
      _ = _ := by dsimp [R]; rw [Real.rpow_add hB0,Real.rpow_one]; ring
  have hN : (witnessSlotCount (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B):ℝ) ≤ 5*R := by
    rw [witnessSlotCount,WitnessConfiguration.codeSlot_card]
    have hM' := hM
    unfold sourceListSlotBudget at hM'
    push_cast at hM' ⊢
    nlinarith
  constructor
  · apply le_trans _ hd
    unfold witnessEntropyDegree
    push_cast
    nlinarith
  · apply le_trans _ (by simpa only [Real.rpow_two] using hb)
    unfold witnessEntropyBase
    have hA := A_pos
    nlinarith

lemma source_witness_prefactor_small (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      sourceWitnessPrefactor C₀ B ≤ Real.exp (B^(1+epsilon/2)) := by
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
  apply (witness_polynomial_bound (sourceSystem B) (sourceListSlotBudget C₀ B)
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

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
