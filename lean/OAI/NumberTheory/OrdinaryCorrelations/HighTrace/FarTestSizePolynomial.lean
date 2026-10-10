import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EventuallyConstPowLeExp
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RootCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarFilling

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

lemma farTestSize_polynomial (B C₀ τ : ℝ) (h : ℕ) (hC : 0≤C₀+4*(h:ℝ)*τ) (hB : 1≤B) :
    farTestSize B C₀ τ h ≤ (C₀+4*(h:ℝ)*τ+2)*B^2 := by
  have hE : 1≤Real.exp ((C₀+4*(h:ℝ)*τ)*B) := Real.one_le_exp (mul_nonneg hC (zero_le_one.trans hB))
  have hl := Real.log_le_log (by positivity : 0<Real.exp ((C₀+4*(h:ℝ)*τ)*B)+2)
    (by linarith : Real.exp ((C₀+4*(h:ℝ)*τ)*B)+2 ≤ 3*Real.exp ((C₀+4*(h:ℝ)*τ)*B))
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] at hl
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  unfold farTestSize
  have hb2 : B≤B^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hb2 hC]

lemma source_far_delta_saving (C₀ τ : ℝ) (h : ℕ) (hC : 0≤C₀+4*(h:ℝ)*τ) :
    ∀ᶠ B : ℝ in atTop,
      max (farTestSize B C₀ τ h/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) ≤
        Real.exp (-(1/2)*B^(1-epsilon)) := by
  let C := (C₀+4*(h:ℝ)*τ+2)/Real.log 2+3
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC' : 0≤C₀+4*(h:ℝ)*τ+2 := by linarith
  filter_upwards [eventually_const_pow_le_exp_rpow C (1-epsilon) (1/2) 2
    (by norm_num [epsilon]) (by norm_num),eventually_ge_atTop (1:ℝ)] with B hp hB
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hP : 0<sourceMinPrime B := Real.exp_pos _
  have hb2 : B≤B^2 := by nlinarith
  have hK := farTestSize_polynomial B C₀ τ h hC hB
  have hmax : max (farTestSize B C₀ τ h/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) ≤ C*B^2/sourceMinPrime B := by
    apply max_le
    · rw [div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ hP.le
      apply (div_le_div_of_nonneg_right hK hlog.le).trans
      dsimp only [C]
      rw [mul_div_right_comm]
      nlinarith [sq_nonneg B]
    · apply div_le_div_of_nonneg_right _ hP.le
      have := div_nonneg hC' hlog.le
      dsimp only [C]
      nlinarith
  apply hmax.trans
  calc
    C*B^2/sourceMinPrime B ≤ Real.exp ((1/2)*B^(1-epsilon))/Real.exp (B^(1-epsilon)) :=
      div_le_div_of_nonneg_right hp hP.le
    _ = _ := by rw [←Real.exp_sub]; congr 1; ring

lemma source_far_root_small (C₀ τ : ℝ) (h : ℕ) (hC : 0≤C₀+4*(h:ℝ)*τ) :
    ∀ᶠ B : ℝ in atTop, ((2*farRootBudget B C₀ τ h+1:ℕ):ℝ) ≤ Real.exp (B^(1+epsilon/2)) := by
  filter_upwards [eventually_const_mul_rpow_le 1 (1+epsilon/2) (C₀+4*(h:ℝ)*τ+5)
    (by norm_num [epsilon]),eventually_ge_atTop (1:ℝ)] with B hdom hB
  have hE : 1≤Real.exp ((C₀+4*(h:ℝ)*τ)*B) := Real.one_le_exp (mul_nonneg hC (zero_le_one.trans hB))
  have hr := (Nat.ceil_lt_add_one (Real.exp_pos ((C₀+4*(h:ℝ)*τ)*B)).le).le
  have h5 : (5:ℝ)≤Real.exp 5 := by linarith [Real.add_one_le_exp (5:ℝ)]
  calc
    _ ≤ 5*Real.exp ((C₀+4*(h:ℝ)*τ)*B) := by unfold farRootBudget; push_cast; linarith
    _ ≤ Real.exp 5*Real.exp ((C₀+4*(h:ℝ)*τ)*B) := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = Real.exp (5+(C₀+4*(h:ℝ)*τ)*B) := (Real.exp_add _ _).symm
    _ ≤ _ := by apply Real.exp_le_exp.mpr; rw [Real.rpow_one] at hdom; nlinarith

namespace NumericalLine
lemma source_far_parameters : ∀ᶠ B : ℝ in atTop,
    0<corruptPathLength B ∧ corruptPathLength B+corruptPathLength B≤pathLength B ∧
    ((((2*sourceLength B)/corruptPathLength B+1)^2*listCutoff B:ℕ):ℝ) ≤ (1/2)*B^(1-2*rho) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num [rho] : 0<(1:ℝ)-3*rho)).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (1-3*rho) (1-rho) 4 (by norm_num [rho]),
    eventually_const_mul_rpow_le (6*rho+4*epsilon) (1-2*rho) 324 (by norm_num [rho,epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hlarge hlen hdom hB
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hx0 : 0<B^(1-3*rho) := Real.rpow_pos_of_pos hB0 _
  have hk : B^(1-3*rho)/2 ≤ (corruptPathLength B:ℝ) := by
    have hx := Nat.lt_floor_add_one (B^(1-3*rho))
    change B^(1-3*rho)/2 ≤ (⌊B^(1-3*rho)⌋₊:ℝ)
    linarith
  have hkpos : 0<corruptPathLength B := Nat.cast_pos.mp ((half_pos hx0).trans_le hk)
  have hku : (corruptPathLength B:ℝ) ≤ B^(1-3*rho) := Nat.floor_le hx0.le
  have hKL : corruptPathLength B+corruptPathLength B≤pathLength B := by
    have hy := Nat.lt_floor_add_one (B^(1-rho))
    change B^(1-rho)<(pathLength B:ℝ)+1 at hy
    apply Nat.cast_le.mp (show ((corruptPathLength B+corruptPathLength B:ℕ):ℝ) ≤ (pathLength B:ℝ) from ?_)
    push_cast
    linarith
  refine ⟨hkpos,hKL,?_⟩
  have hq := Nat.div_mul_le_self (2*sourceLength B) (corruptPathLength B)
  have hq' : (((2*sourceLength B)/corruptPathLength B:ℕ):ℝ)*(corruptPathLength B:ℝ) ≤ 2*(sourceLength B:ℝ) := by exact_mod_cast hq
  have hl := sourceLength_le B hB0.le
  have hex : B^(1-3*rho)*B^(3*rho)=B := by
    rw [←Real.rpow_add hB0]
    convert Real.rpow_one B using 1
    ring_nf
  have hQ : (((2*sourceLength B)/corruptPathLength B+1:ℕ):ℝ) ≤ 9*B^(3*rho) := by
    have hnon : 0≤(((2*sourceLength B)/corruptPathLength B:ℕ):ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hk hnon
    have hpre : (((2*sourceLength B)/corruptPathLength B:ℕ):ℝ) ≤ 8*B^(3*rho) := by nlinarith
    have hone : 1≤B^(3*rho) := Real.one_le_rpow hB (by norm_num [rho])
    push_cast
    linarith
  have ht : (listCutoff B:ℝ) ≤ 2*B^(4*epsilon) := ceil_rpow_le_two B (4*epsilon) hB (by norm_num [epsilon])
  have hb : ((((2*sourceLength B)/corruptPathLength B+1)^2*listCutoff B:ℕ):ℝ) ≤ 162*B^(6*rho+4*epsilon) := by
    push_cast
    calc
      _ ≤ (9*B^(3*rho))^2*(2*B^(4*epsilon)) := by
        gcongr
        simpa only [Nat.cast_add,Nat.cast_one] using hQ
      _ = 162*((B^(3*rho))^2*B^(4*epsilon)) := by ring
      _ = _ := by
        rw [←Real.rpow_mul_natCast hB0.le,←Real.rpow_add hB0]
        congr 2
        norm_num
        ring
  linarith

theorem source_many_far_small (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) (hτ : 0≤τ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      manyFarSum D h (sourceLength B) (pathLength B) (corruptPathLength B) (listCutoff B) cut ≤
        Real.exp (-B^(1+epsilon/2)) := by
  have hC : 0≤C₀+4*(h:ℝ)*τ := by positivity
  filter_upwards [source_packed_gap_prefactor_small C₀ hC₀,
    source_far_delta_saving C₀ τ h hC,source_far_root_small C₀ τ h hC, source_far_parameters,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+3*epsilon) 6 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hdelta hroot hparam hdom hB
  intro D cut
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hP : 0<sourceMinPrime B := Real.exp_pos _
  have htpos : 0<listCutoff B := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hB0 _)
  have hb := manyFarSum_bound (D:=D) (L:=pathLength B) hh cut (sourceMinPrime B) hP hB0.le hparam.1 htpos hτ
    (sourceLength_le B hB0.le) (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩)
  have hp : packedGapPrefactor (sourceSystem B) (sourceLength B) (corruptPathLength B+corruptPathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B) ≤
      Real.exp (B^(1+epsilon/2)) :=
    (packedGapPrefactor_mono_path _ _ _ _ _ _ hparam.2.1).trans hpref
  have ht : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hs : (1/2)*B^(1+3*epsilon) ≤ (listCutoff B:ℝ)*((1/2)*B^(1-epsilon)) := by
    have hm := mul_le_mul_of_nonneg_right ht (show 0≤(1/2)*B^(1-epsilon) by positivity)
    have he : B^(4*epsilon)*((1/2)*B^(1-epsilon))=(1/2)*B^(1+3*epsilon) := by
      rw [mul_left_comm,←Real.rpow_add hB0]
      congr 2
      ring
    rwa [he] at hm
  have hδ0 : 0 ≤ max (farTestSize B C₀ τ h/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) :=
    le_trans (by positivity : 0≤(2+B)/sourceMinPrime B) (le_max_right _ _)
  apply hb.trans
  apply (mul_le_mul (mul_le_mul hroot hp (by unfold packedGapPrefactor; positivity [A_pos]) (Real.exp_pos _).le)
    (pow_le_pow_left₀ hδ0 hdelta _) (pow_nonneg hδ0 _) (by positivity)).trans
  rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma farCorruptSum_le_manyFarSum {B τ T C₀ : ℝ} {h : ℕ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) (cut : (sourceSystem B).Cutoffs T)
    (hthreshold : ((((2*sourceLength B)/corruptPathLength B+1)^2*listCutoff B:ℕ):ℝ) ≤ (1/2)*B^(1-2*rho)) :
    farCorruptSum D h (sourceLength B) cut ≤ manyFarSum D h (sourceLength B) (pathLength B) (corruptPathLength B) (listCutoff B) cut := by
  unfold farCorruptSum manyFarSum
  apply sum_le_sum
  intro w _
  apply avg_mono
  intro r
  by_cases hn : (1/2)*B^(1-2*rho) ≤ ((farCorrupted w (corruptPathLength B)).card:ℝ)
  · have hm : w.ManyFarCorrupted (corruptPathLength B) (listCutoff B) := Nat.cast_le.mp (hthreshold.trans hn)
    simp only [hn,hm,ite_true,le_refl]
  · rw [ite_eq_right hn]
    split_ifs <;> positivity

theorem source_far_corrupt_small (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) (hτ : 0≤τ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      farCorruptSum D h (sourceLength B) cut ≤ Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_many_far_small h hh τ T C₀ hτ hC₀,source_far_parameters] with B hsmall hp
  intro D cut
  exact (farCorruptSum_le_manyFarSum D cut hp.2.2).trans (hsmall D cut)

theorem source_corrupted_small (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) (hτ : 0≤τ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      corruptedErrorSum D (h:=h) (ℓ:=sourceLength B) cut ≤ 2*Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_near_corrupt_small h τ T C₀ hC₀,
    source_far_corrupt_small h hh τ T C₀ hτ hC₀,
    source_near_corrupt_threshold C₀ hC₀,eventually_ge_atTop (1:ℝ)] with B hn hf hthreshold hB
  intro D cut
  have hc := corrupted_near_far_of_threshold (h:=h) (ℓ:=sourceLength B) D cut hthreshold
  have hnear := hn D cut (corruptPathLength B) (corruptPathLength_le B hB)
  have hfar := hf D cut
  linarith

theorem source_full_trace_disconnected (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+4*Real.exp (-B^(1+epsilon/2))+
          disconnectedErrorSum D (ℓ:=sourceLength B) hh cut := by
  filter_upwards [source_full_trace_near_far h hh τ T C₀ hτ hτ2 hC₀,
    source_far_corrupt_small h hh τ T C₀ (zero_le_one.trans hτ) hC₀] with B ht hf
  intro D cut
  have := ht D cut
  have := hf D cut
  linarith

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
