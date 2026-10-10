import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessBasicScales

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical Filter

lemma eventually_const_pow_le_exp_rpow (C a c : ℝ) (n : ℕ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ B : ℝ in atTop, C*B^n ≤ Real.exp (c*B^a) := by
  let D := max 1 C
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hl := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have hi : Tendsto (fun B : ℝ => Real.log D / B^a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
  have ht := hi.add (hl.const_mul (n:ℝ))
  simp only [mul_zero,add_zero] at ht
  filter_upwards [ht.eventually (eventually_le_nhds hc),eventually_gt_atTop (0:ℝ)] with B hb hB
  have hb' : Real.log D+(n:ℝ)*Real.log B ≤ c*B^a := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hB _)).mp
    simpa only [add_div,mul_div_assoc] using hb
  calc
    _ ≤ D*B^n := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hB.le _)
    _ = Real.exp (Real.log D+(n:ℝ)*Real.log B) := by
      rw [Real.exp_add,Real.exp_log hD,Real.exp_nat_mul,Real.exp_log hB]
    _ ≤ _ := Real.exp_le_exp.mpr hb'

lemma source_testSize_polynomial (h : ℕ) (C₀ B : ℝ) (hC₀ : 0 ≤ C₀) (hB : 1 ≤ B) :
    PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B) ≤
      (C₀+4*(h:ℝ)+3)*B^2 := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hℓ := sourceLength_le B hB0.le
  have hL := pathLength_le B hB
  have hJ := divisorSlots_le B C₀ hB hC₀
  have hE : 1 ≤ Real.exp (B*(⌈C₀*Real.log B⌉₊:ℝ)) := Real.one_le_exp (by positivity)
  have hsz : (((sourceLength B+pathLength B+pathLength B:ℕ):ℝ)*h*
      Real.exp (B*⌈C₀*Real.log B⌉₊)+2) ≤
      ((((sourceLength B+pathLength B+pathLength B:ℕ):ℝ)*h+2)*
        Real.exp (B*⌈C₀*Real.log B⌉₊)) := by nlinarith
  have hbase0 : 0 < (((sourceLength B+pathLength B+pathLength B:ℕ):ℝ)*h+2) := by positivity
  have hl := Real.log_le_log (by positivity : 0 <
    (((sourceLength B+pathLength B+pathLength B:ℕ):ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊)+2)) hsz
  rw [Real.log_mul hbase0.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  have hh := Real.log_le_sub_one_of_pos hbase0
  have hJB := mul_le_mul_of_nonneg_left hJ hB0.le
  have hb2 : B ≤ B^2 := by nlinarith
  have hh0 : 0 ≤ (h:ℝ) := Nat.cast_nonneg _
  have hsum : (((sourceLength B+pathLength B+pathLength B:ℕ):ℝ)*h) ≤ 4*B*h := by
    push_cast
    nlinarith
  unfold PrivateFamily.testSize
  nlinarith

lemma source_witness_delta_saving (C₀ : ℝ) (h : ℕ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      sourceWitnessDelta C₀ h B ≤ Real.exp (-(1/2)*B^(1-epsilon)) := by
  let C := (C₀+4*(h:ℝ)+3)/Real.log 2+3
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C₀+4*(h:ℝ)+3 := by positivity
  filter_upwards [eventually_const_pow_le_exp_rpow C (1-epsilon) (1/2) 2
    (by norm_num [epsilon]) (by norm_num),eventually_ge_atTop (1:ℝ)] with B hp hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hb2 : B ≤ B^2 := by nlinarith
  have hK := source_testSize_polynomial h C₀ B hC₀ hB
  have hmax : sourceWitnessDelta C₀ h B ≤ C*B^2/sourceMinPrime B := by
    unfold sourceWitnessDelta
    apply max_le
    · rw [div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ hP.le
      apply (div_le_div_of_nonneg_right hK hlog.le).trans
      dsimp only [C]
      rw [mul_div_right_comm]
      nlinarith [sq_nonneg B]
    · apply div_le_div_of_nonneg_right _ hP.le
      have := div_nonneg hC hlog.le
      dsimp only [C]
      nlinarith
  apply hmax.trans
  calc
    C*B^2/sourceMinPrime B ≤ Real.exp ((1/2)*B^(1-epsilon))/Real.exp (B^(1-epsilon)) :=
      div_le_div_of_nonneg_right hp hP.le
    _ = _ := by rw [←Real.exp_sub]; congr 1; ring

lemma source_witness_delta_nonneg (C₀ B : ℝ) (h : ℕ) (hB : 0 ≤ B) :
    0 ≤ sourceWitnessDelta C₀ h B := by
  apply le_trans _ (le_max_right _ _)
  unfold sourceMinPrime
  positivity

lemma source_witness_delta_power (C₀ : ℝ) (h : ℕ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      sourceWitnessDelta C₀ h B ≤ 1 ∧
      (sourceWitnessDelta C₀ h B)^⌈B^(2*epsilon)⌉₊ ≤
        Real.exp (-(1/2)*B^(1+epsilon)) := by
  filter_upwards [source_witness_delta_saving C₀ h hC₀,eventually_ge_atTop (1:ℝ)] with B hd hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hpos : 0 ≤ sourceWitnessDelta C₀ h B := source_witness_delta_nonneg C₀ B h hB0.le
  have hc : B^(2*epsilon) ≤ (⌈B^(2*epsilon)⌉₊:ℝ) := Nat.le_ceil _
  constructor
  · exact hd.trans (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg hB0.le _)))
  · apply (pow_le_pow_left₀ hpos hd _).trans
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonpos_right hc (show -(1/2)*B^(1-epsilon) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg hB0.le _))
    apply hm.trans_eq
    calc
      _ = -(1/2)*(B^(2*epsilon)*B^(1-epsilon)) := by ring
      _ = _ := by rw [←Real.rpow_add hB0]; congr 2; ring

theorem source_witness_majorant_small (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ)
    (hτ : τ < 2) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀),
      NumericalLine.sourceWitnessMajorant D h ≤ Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_witness_majorant_envelope h hh τ C₀ hτ,
    source_witness_prefactor_small C₀ hC₀,source_witness_delta_power C₀ h hC₀,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+epsilon) 4 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B he hp hd hlarge hB
  intro D
  apply (he D hd.1).trans
  apply (mul_le_mul hp hd.2
    (pow_nonneg (source_witness_delta_nonneg C₀ B h (zero_le_one.trans hB)) _)
    (Real.exp_pos _).le).trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
