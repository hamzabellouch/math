import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceCoreEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalCodeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CodeEntropyMass

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

noncomputable def exceptionalBudget (B : ℝ) : ℕ := ⌈B^(1-rho/2)⌉₊

lemma eventually_const_mul_rpow_le (a b C : ℝ) (hab : a < b) :
    ∀ᶠ B : ℝ in atTop, C*B^a ≤ B^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,
    eventually_gt_atTop (0:ℝ)] with B h hB
  calc
    _ ≤ B^(b-a)*B^a := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hB.le _)
    _ = _ := by rw [← Real.rpow_add hB]; congr 1; ring

lemma eventually_log_ceil_le (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a) :
    ∀ᶠ B : ℝ in atTop, (⌈C*Real.log B⌉₊:ℝ) ≤ B^a := by
  have hl := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have hi : Tendsto (fun B : ℝ => (1:ℝ)/B^a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
  have ht := (hl.const_mul C).add hi
  simp only [mul_zero,add_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (1:ℝ)] with B h hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hc := Nat.ceil_lt_add_one (mul_nonneg hC (Real.log_nonneg hB))
  have hdiv : (C*Real.log B+1)/B^a < 1 := by simpa only [add_div,mul_div_assoc] using h
  have hb := (div_lt_one (Real.rpow_pos_of_pos hB0 _)).mp hdiv
  exact hc.le.trans hb.le

lemma ceil_rpow_le_two (B a : ℝ) (hB : 1 ≤ B) (ha : 0 ≤ a) :
    (⌈B^a⌉₊:ℝ) ≤ 2*B^a := by
  have hpos : 0 ≤ B^a := Real.rpow_nonneg (zero_le_one.trans hB) _
  have hpow : 1 ≤ B^a := Real.one_le_rpow hB ha
  linarith [Nat.ceil_lt_add_one hpos]

lemma source_entropy_scales (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      1 ≤ B ∧
      (listCutoff B:ℝ) ≤ B^(rho/8) ∧
      (⌈C₀*Real.log B⌉₊:ℝ) ≤ B^(rho/8) ∧
      (pathLength B:ℝ) ≤ B^(1-rho) ∧
      (exceptionalBudget B:ℝ) ≤ 2*B^(1-rho/2) := by
  filter_upwards [eventually_const_mul_rpow_le (4*epsilon) (rho/8) 2
      (by norm_num [rho,epsilon]),eventually_log_ceil_le C₀ (rho/8) hC₀ (by norm_num [rho]),
    eventually_ge_atTop (1:ℝ)] with B hn hJ hB
  refine ⟨hB,?_,hJ,?_,?_⟩
  · exact (ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])).trans hn
  · exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hB) _)
  · exact ceil_rpow_le_two B (1-rho/2) hB (by norm_num [rho])

namespace RecordPacket
lemma codeEntropyMass_eq (S : PrimeSystem) :
    codeEntropyMass S = S.harmonicCore+S.harmonicCenter := by
  exact (Fintype.sum_subtype_add_sum_subtype S.IsCore (fun p : S.Index => (p:ℝ)⁻¹)).symm

lemma source_mass_le_log : ∀ᶠ B : ℝ in atTop,
    codeEntropyMass (sourceSystem B) ≤ Real.log B := by
  have h := SourcePrimeBands.source_prime_bands.1.add SourcePrimeBands.source_prime_bands.2
  have ht : SourcePrimeBands.eta+(SourcePrimeBands.epsilon-SourcePrimeBands.eta) < 1 := by
    norm_num [SourcePrimeBands.epsilon,SourcePrimeBands.eta]
  filter_upwards [h.eventually (eventually_lt_nhds ht),eventually_gt_atTop (1:ℝ)] with B hB hpos
  rw [← add_div] at hB
  have hh := (div_lt_one (Real.log_pos hpos)).mp hB
  simpa only [codeEntropyMass_eq,source_harmonicCore,source_harmonicCenter] using hh.le

lemma source_entropy_degree_bound (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      (codeEntropyDegree (pathLength B) (listCutoff B)
        (Fintype.card (ExceptionalCodeSlot (pathLength B) ⌈C₀*Real.log B⌉₊
          (listCutoff B) (exceptionalBudget B))) (exceptionalBudget B):ℝ) ≤
        B^(1-rho/4) := by
  filter_upwards [source_entropy_scales C₀ hC₀,
    eventually_const_mul_rpow_le (1-rho/2) (1-rho/4) 16 (by norm_num [rho])] with B hs hbig
  obtain ⟨hB,hn,hJ,hL,hN⟩ := hs
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hn0 : 0 ≤ (listCutoff B:ℝ) := Nat.cast_nonneg _
  have hnL : (listCutoff B:ℝ)*(pathLength B:ℝ) ≤ B^(1-rho/2) := by
    calc
      _ ≤ B^(rho/8)*B^(1-rho) := mul_le_mul hn hL (Nat.cast_nonneg _) (Real.rpow_nonneg hB0.le _)
      _ = B^(rho/8+(1-rho)) := (Real.rpow_add hB0 ..).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho])
  have hnLJ : (listCutoff B:ℝ)*((pathLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ)) ≤ B^(1-rho/2) := by
    calc
      _ ≤ B^(rho/8)*(B^(1-rho)*B^(rho/8)) := mul_le_mul hn
        (mul_le_mul hL hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hB0.le _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.rpow_nonneg hB0.le _)
      _ = B^(rho/8+((1-rho)+rho/8)) := by rw [Real.rpow_add hB0,Real.rpow_add hB0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho])
  have hn' : (listCutoff B:ℝ) ≤ B^(1-rho/2) := hn.trans
    (Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho]))
  have h1 : (1:ℝ) ≤ B^(1-rho/2) := Real.one_le_rpow hB (by norm_num [rho])
  rw [codeEntropyDegree,exceptionalCodeSlot_card]
  push_cast
  nlinarith

lemma source_entropy_base_bound (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      codeEntropyBase (sourceSystem B) (sourceLength B) (pathLength B)
        (listCutoff B) (exceptionalBudget B) C₀ B ≤ B^2 := by
  filter_upwards [source_entropy_scales C₀ hC₀,source_mass_le_log,
    eventually_ge_atTop (14:ℝ)] with B hs hm h14
  obtain ⟨hB,hn,hJ,hL,hN⟩ := hs
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hnLJ : (listCutoff B:ℝ)*((pathLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ)) ≤ B := by
    calc
      _ ≤ B^(rho/8)*(B^(1-rho)*B^(rho/8)) := mul_le_mul hn
        (mul_le_mul hL hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hB0.le _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.rpow_nonneg hB0.le _)
      _ = B^(rho/8+((1-rho)+rho/8)) := by rw [Real.rpow_add hB0,Real.rpow_add hB0]
      _ ≤ B^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho])
      _ = B := Real.rpow_one _
  have hn' : (listCutoff B:ℝ) ≤ B := hn.trans (Real.rpow_le_self_of_one_le hB (by norm_num [rho]))
  have hN' : (exceptionalBudget B:ℝ) ≤ 2*B := hN.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_self_of_one_le hB (by norm_num [rho])) (by norm_num))
  have hL' := pathLength_le B hB
  have hℓ := sourceLength_le B hB0.le
  have hmass : codeEntropyMass (sourceSystem B) ≤ B := hm.trans ((Real.log_le_sub_one_of_pos hB0).trans (by linarith))
  unfold codeEntropyBase
  rw [exceptionalCodeSlot_card]
  push_cast
  nlinarith

theorem source_entropy_sublinear (C₀ c : ℝ) (hC₀ : 0 ≤ C₀) (hc : 0 < c) :
    ∀ᶠ B : ℝ in atTop,
      (Fintype.card (ListMetadata (sourceLength B) (pathLength B) (listCutoff B)):ℝ) *
        exceptionalCost (sourceSystem B) (sourceLength B) (pathLength B)
          (listCutoff B) (exceptionalBudget B) C₀ B ≤ Real.exp (c*B) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num [rho] : 0 < rho/4)).tendsto_div_nhds_zero
  filter_upwards [source_entropy_degree_bound C₀ hC₀,source_entropy_base_bound C₀ hC₀,
    hlim.eventually (eventually_le_nhds (show (0:ℝ)<c/2 by positivity)),
    eventually_ge_atTop (1:ℝ)] with B hd hq hh hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let D := codeEntropyDegree (pathLength B) (listCutoff B)
    (Fintype.card (ExceptionalCodeSlot (pathLength B) ⌈C₀*Real.log B⌉₊
      (listCutoff B) (exceptionalBudget B))) (exceptionalBudget B)
  have hQ0 := codeEntropyBase_ge_two (sourceSystem B) (sourceLength B) (pathLength B)
    (listCutoff B) (exceptionalBudget B) C₀ B
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ codeEntropyBase (sourceSystem B)
    (sourceLength B) (pathLength B) (listCutoff B) (exceptionalBudget B) C₀ B) hq D
  have hb : (B^2)^D ≤ Real.exp (c*B) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (sq_pos_of_pos hB0),Real.log_pow]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_nonneg hB
    have hp := Real.rpow_pos_of_pos hB0 (rho/4)
    have hmul := (div_le_iff₀ hp).mp hh
    have h := mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hB0.le (1-rho/4))
    have he : B^(1-rho/4)*(c/2*B^(rho/4)) = (c/2)*B := by
      rw [mul_left_comm,← Real.rpow_add hB0]
      congr 1
      rw [show (1-rho/4)+rho/4=1 by ring,Real.rpow_one]
    rw [he] at h
    have hdl := mul_le_mul_of_nonneg_right hd hlog
    dsimp only [D] at *
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  exact packet_entropy_polynomial.trans (hp.trans hb)

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
