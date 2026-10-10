import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Primes

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourcePrimeBoxSieve
open Classical Finset Real Filter
open SourceRoughSieveLocal SourceBoxSieve SourceBonferroni

lemma primitive_two_lower : -3 ≤ SourcePrimeReciprocal.primitive 2 := by
  have hlo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hhi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hl : -1 ≤ Real.log (Real.log 2) := by
    calc
      _ ≤ -Real.log 2 := by linarith
      _ = Real.log (1/2:ℝ) := by rw [one_div,Real.log_inv]
      _ ≤ _ := Real.log_le_log (by norm_num) hlo
  have hi : (Real.log 2)⁻¹ ≤ 2 := by
    have h := inv_anti₀ (by norm_num : (0:ℝ)<1/2) hlo
    norm_num at h
    exact h
  unfold SourcePrimeReciprocal.primitive
  linarith

lemma source_local_sum (L : ℝ) (hL : 1 < L) (hlog : 1 ≤ Real.log L)
    (K : ℕ) (hK : 2 ≤ K) (hKy : (K:ℝ) ≤ Real.exp (L^(99/100:ℝ))) :
    (∑ p : Primes K, badDensity p.val) ≤ 100*Real.log L := by
  have hLp : 0 < L := by linarith
  have hKp : (1:ℝ)<K := by exact_mod_cast (show 1<K by omega)
  have hll : Real.log (Real.log (K:ℝ)) ≤ (99/100:ℝ)*Real.log L := by
    have hl := Real.log_le_log (by linarith : (0:ℝ)<K) hKy
    rw [Real.log_exp] at hl
    have h := Real.log_le_log (Real.log_pos hKp) hl
    rwa [Real.log_rpow hLp] at h
  have hc : 0 ≤ 4*Real.log 4 := by positivity
  have hd : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    norm_num at h ⊢
    exact h
  calc
    _ ≤ 4*Real.log 4*(Real.log (Real.log (K:ℝ))-SourcePrimeReciprocal.primitive 2) := local_sum_bound K hK
    _ ≤ 4*Real.log 4*(Real.log L+3) :=
      mul_le_mul_of_nonneg_left (by linarith [primitive_two_lower]) hc
    _ ≤ 12*(Real.log L+3) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ ≤ _ := by linarith

lemma coarse_source_tail {ι : Type*} [DecidableEq ι] (P : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ P, 0 ≤ v i) (L : ℝ) (hL : 1 ≤ L)
    (hS : (∑ i ∈ P, v i) ≤ 100*Real.log L) (k : ℕ) (hk : 1000*Real.log L ≤ k) :
    elementary P v k ≤ L^(-100:ℝ) := by
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h ⊢
    exact h
  have he : (2:ℝ)^k = Real.exp ((k:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ Real.exp (2*∑ i ∈ P, v i)/(2:ℝ)^k := elementary_le_exp P v hv k
    _ = Real.exp (2*∑ i ∈ P, v i-(k:ℝ)*Real.log 2) := by rw [he,Real.exp_sub]
    _ ≤ Real.exp ((-100)*Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k)
      nlinarith
    _ = _ := by rw [Real.rpow_def_of_pos hLp]; congr 1; ring

lemma primes_card (K : ℕ) : Fintype.card (Primes K) ≤ K+1 := by
  rw [Fintype.card_coe]
  calc
    _ ≤ (range (K+1)).card := Finset.card_le_card (by
      intro p hp
      exact Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1)
    _ = _ := Finset.card_range _

lemma source_boundary_numerator (L : ℝ) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (K : ℕ) (hKy : (K:ℝ) ≤ Real.exp (L^(99/100:ℝ))) :
    3*(2*⌈500*Real.log L⌉₊+1:ℕ)*
      (((Fintype.card (Primes K):ℝ)+1)*K)^(2*⌈500*Real.log L⌉₊) ≤
        Real.exp (8000*L^(99/100:ℝ)*Real.log L) := by
  let t := L^(99/100:ℝ)
  let R := 2*⌈500*Real.log L⌉₊
  have ht : 1 ≤ t := Real.one_le_rpow hL (by norm_num)
  have he : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
  have hc : (Fintype.card (Primes K):ℝ)+1 ≤ 3*Real.exp t := by
    have h := primes_card K
    have hc' : (Fintype.card (Primes K):ℝ) ≤ (K:ℝ)+1 := by exact_mod_cast h
    dsimp [t] at he ⊢
    linarith
  have hb : ((Fintype.card (Primes K):ℝ)+1)*K ≤ Real.exp (4*t) := by
    have h3 : (3:ℝ) ≤ Real.exp (2*t) := by
      have h := Real.add_one_le_exp (2*t)
      linarith
    calc
      _ ≤ (3*Real.exp t)*Real.exp t := mul_le_mul hc hKy (by positivity) (by positivity)
      _ = 3*Real.exp (2*t) := by rw [show 2*t=t+t by ring,Real.exp_add]; ring
      _ ≤ Real.exp (2*t)*Real.exp (2*t) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hR : (R:ℝ) ≤ 1002*Real.log L := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 500*Real.log L by linarith)
    dsimp [R]
    push_cast
    linarith
  have hfac : 3*(R+1:ℕ) ≤ Real.exp (3010*Real.log L) := by
    have hh := Real.add_one_le_exp (3010*Real.log L)
    push_cast
    linarith
  change 3*(R+1:ℕ)*(((Fintype.card (Primes K):ℝ)+1)*K)^R ≤ _
  calc
    _ ≤ Real.exp (3010*Real.log L)*(Real.exp (4*t))^R :=
      mul_le_mul hfac (pow_le_pow_left₀ (by positivity) hb R) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (3010*Real.log L+(R:ℝ)*(4*t)) := by rw [← Real.exp_nat_mul,← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change 3010*Real.log L+(R:ℝ)*(4*t) ≤ 8000*t*Real.log L
      have hh := mul_le_mul_of_nonneg_right hR (show 0 ≤ 4*t by linarith)
      have hh' := mul_le_mul_of_nonneg_right ht (show 0 ≤ Real.log L by linarith)
      nlinarith

lemma eventually_boundary_margin : ∀ᶠ L : ℝ in atTop,
    8000*L^(99/100:ℝ)*Real.log L + Real.log 2 + 100*Real.log L ≤ L^(199/200:ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop (r := (1/200:ℝ)) (by norm_num)).bound
    (c := (1/10000:ℝ)) (by norm_num)
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)
  filter_upwards [hlog,hlarge,eventually_ge_atTop (1:ℝ)] with L hh hl hL
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Real.log L),
    abs_of_nonneg (Real.rpow_pos_of_pos hLp _).le] at hh
  have ht : 1 ≤ L^(99/100:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hm : L^(99/100:ℝ)*L^(1/200:ℝ) = L^(199/200:ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hprod := mul_le_mul_of_nonneg_left hh (show 0 ≤ L^(99/100:ℝ) by positivity)
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hh' := mul_le_mul_of_nonneg_right ht (show 0 ≤ Real.log L by linarith)
  nlinarith

lemma source_boundary_small (L : ℝ) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hm : 8000*L^(99/100:ℝ)*Real.log L + Real.log 2 + 100*Real.log L ≤ L^(199/200:ℝ))
    (K N : ℕ) (hN : 0 < N) (hKy : (K:ℝ) ≤ Real.exp (L^(99/100:ℝ)))
    (hD : (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ N) :
    3*(2*⌈500*Real.log L⌉₊+1:ℕ)*
      (((Fintype.card (Primes K):ℝ)+1)*K)^(2*⌈500*Real.log L⌉₊)/N ≤ L^(-100:ℝ) := by
  calc
    _ ≤ Real.exp (8000*L^(99/100:ℝ)*Real.log L)/(N:ℝ) :=
      div_le_div_of_nonneg_right (source_boundary_numerator L hL hlog K hKy) (by positivity)
    _ ≤ Real.exp (8000*L^(99/100:ℝ)*Real.log L)/((1/2:ℝ)*Real.exp (L^(199/200:ℝ))) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hD
    _ = Real.exp (8000*L^(99/100:ℝ)*Real.log L+Real.log 2-L^(199/200:ℝ)) := by
      rw [Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring
    _ ≤ Real.exp ((-100)*Real.log L) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.rpow_def_of_pos (show 0<L by linarith)]; congr 1; ring

end OrdinaryCorrelations.SourcePrimeBoxSieve

end

end OAI
