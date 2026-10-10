import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Grid

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

namespace OrdinarySparsePowerScales
open Filter Finset OrdinaryNarrowGrid

lemma two_power_ratio_limit (a b m : ℕ) (h : a < b) :
    Tendsto (fun n : ℕ => (n:ℝ)^m*(2:ℝ)^(a*n)/(2:ℝ)^(b*n)) atTop (nhds 0) := by
  have hr : (2:ℝ)^a/(2:ℝ)^b < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ (by norm_num) h
  convert tendsto_pow_const_mul_const_pow_of_lt_one m (by positivity) hr using 1
  ext n
  simp only [pow_mul,div_pow]
  ring

lemma eventually_two_power (q : ℕ) : ∀ᶠ n : ℕ in atTop, q ≤ 2^n := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ) < 2)).eventually_ge_atTop q

lemma prime_product_squarefree (S : Finset ℕ) (hS : ∀ p∈S, Nat.Prime p) :
    Squarefree (∏ p∈S,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact (Nat.coprime_iff_isRelPrime).mp ((hS p hp).coprime_iff_not_dvd.mpr (by
      intro hd
      exact hpq ((Nat.dvd_prime (hS q hq)).mp hd |>.resolve_left (hS p hp).ne_one)))
  · exact fun p hp => (hS p hp).squarefree

lemma grid_scales (q s k n : ℕ) (hq : 0 < q) (hs : 1 ≤ s)
    (hsk : s+1 ≤ 8*k) (hqpow : q ≤ 2^n) :
    ∀ i∈grid q n ((s-1)*n),
      2^((8*k-s-1)*n)  ≤  (2*2^(8*k*n))/(2*lower i) ∧
      (2*2^(8*k*n))/(2*lower i)  ≤  (2^(k*n))^8 := by
  intro i hi
  have ha : 0 < lower i := grid_lower_pos q n ((s-1)*n) hq hi
  have hend : n+(s-1)*n=s*n := by
    calc
      _ = (s-1+1)*n := by ring
      _ = _ := by rw [Nat.sub_add_cancel hs]
  have hau : lower i ≤ q*2^(s*n) := by
    have hh := (lower_le_upper i).trans (upper_le_endpoint q n ((s-1)*n) hi)
    rwa [hend] at hh
  have hmul : 2^((8*k-s-1)*n)*(q*2^(s*n))  ≤  2^(8*k*n) := by
    calc
      _  ≤  2^((8*k-s-1)*n)*(2^n*2^(s*n)) := by gcongr
      _ = 2^(8*k*n) := by
        rw [←pow_add,←pow_add]
        congr 1
        calc
          _ = (8*k-s-1+s+1)*n := by ring
          _ = _ := by rw [show 8*k-s-1+s+1=8*k by omega]
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2*lower i)).mpr
    have hh := (Nat.mul_le_mul_left (2^((8*k-s-1)*n)) hau).trans hmul
    nlinarith
  · rw [←pow_mul]
    have he : k*n*8=8*k*n := by ring
    rw [he]
    rw [Nat.mul_div_mul_left _ _ (by norm_num : 0<2)]
    exact Nat.div_le_self _ _

lemma grid_height (q k n : ℕ) (hq : 0 < q) (hk : 0 < k) (hn : 0 < n)
    (T : Finset ℝ) (hT : ∀ t∈T, |t| ≤ (2:ℝ)^(9*k*n)) :
    (∀ t∈T, ∀ s∈T, |t-s| ≤ ((2^(k*n):ℕ):ℝ)^10) ∧
    (∀ t∈T, |t| ≤ ((q*2^n:ℕ):ℝ)^(9*k+1)/2) := by
  have he : k*n*10=10*k*n := by ring
  constructor
  · intro t ht s hs
    calc
      |t-s|  ≤  |t|+|s| := abs_sub _ _
      _  ≤  2*(2:ℝ)^(9*k*n) := by linarith [hT t ht,hT s hs]
      _ = (2:ℝ)^(9*k*n+1) := by rw [pow_succ]; ring
      _  ≤  _ := by
        push_cast
        rw [←pow_mul,he]
        exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
  · intro t ht
    apply (hT t ht).trans
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    calc
      _ = (2:ℝ)^(9*k*n+1) := by rw [pow_succ]
      _  ≤  (2:ℝ)^(n*(9*k+1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith
      _ = ((2^n:ℕ):ℝ)^(9*k+1) := by push_cast; rw [pow_mul]
      _  ≤  _ := by gcongr; exact_mod_cast (Nat.le_mul_of_pos_left (2^n) hq)

lemma eventually_small_errors (d s k q : ℕ) (hk : s+4*d+4 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ q ≤ 2^n ∧
      3200*(2:ℝ)^n*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7 /
        ((2^((8*k-s-1)*n):ℕ):ℝ) ≤ 1/(n:ℝ) ∧
      3200*(2:ℝ)^n*((2^(k*n):ℕ):ℝ)^7/((2^(8*k*n):ℕ):ℝ) ≤ 1 ∧
      10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) ≤ δ := by
  have ha : 1+4*d+7*k < 8*k-s-1 := by omega
  have hb : 1+7*k < 8*k := by omega
  have hc : s+4*d < 8*k := by omega
  have hlim₁ := (two_power_ratio_limit (1+4*d+7*k) (8*k-s-1) 1 ha).const_mul 3200
  have hlim₂ := (two_power_ratio_limit (1+7*k) (8*k) 0 hb).const_mul 3200
  have hlim₃ := (two_power_ratio_limit (s+4*d) (8*k) 0 hc).const_mul (10*(q:ℝ))
  simp only [mul_zero] at hlim₁ hlim₂ hlim₃
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_two_power q,
    hlim₁.eventually_le_const (by norm_num : (0:ℝ)<1),
    hlim₂.eventually_le_const (by norm_num : (0:ℝ)<1),
    hlim₃.eventually_le_const hδ] with n hn hq h₁ h₂ h₃
  refine ⟨hn,hq,?_,?_,?_⟩
  · have he : (2:ℝ)^n*((2^(d*n):ℕ):ℝ)^4*((2^(k*n):ℕ):ℝ)^7 =
        (2:ℝ)^((1+4*d+7*k)*n) := by
      push_cast
      rw [←pow_mul,←pow_mul,←pow_add,←pow_add]
      congr 1
      ring
    apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
    convert h₁ using 1
    push_cast
    · rw [←he]
      push_cast
      ring
  · have he : (2:ℝ)^n*((2^(k*n):ℕ):ℝ)^7 = (2:ℝ)^((1+7*k)*n) := by
      push_cast
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    apply le_trans (le_of_eq ?_) h₂
    rw [←he]
    push_cast
    ring
  · simpa only [pow_zero,one_mul,mul_div_assoc] using h₃

lemma floor_error_bound (q d s k n : ℕ) (hs : 1 ≤ s) :
    (((q*2^n:ℕ):ℝ)*((2^(d*n):ℕ):ℝ)^4 +
      (32+4*((2^(d*n):ℕ):ℝ)^4)*((q*2^(s*n):ℕ):ℝ))/(4*((2^(8*k*n):ℕ):ℝ)) ≤
      10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n) := by
  have hp : (2:ℝ)^n ≤ (2:ℝ)^(s*n) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.le_mul_of_pos_left n hs
  have hz : (1:ℝ) ≤ ((2^(d*n):ℕ):ℝ)^4 := by
    push_cast
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have h₁ : (((q*2^n:ℕ):ℝ)*((2^(d*n):ℕ):ℝ)^4) ≤
      (q:ℝ)*(2:ℝ)^(s*n)*((2^(d*n):ℕ):ℝ)^4 := by push_cast; gcongr
  have h₂ : (32+4*((2^(d*n):ℕ):ℝ)^4)*((q*2^(s*n):ℕ):ℝ) ≤
      36*(q:ℝ)*(2:ℝ)^(s*n)*((2^(d*n):ℕ):ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_right (by linarith :
      32+4*((2^(d*n):ℕ):ℝ)^4 ≤ 36*((2^(d*n):ℕ):ℝ)^4)
      (by positivity : 0 ≤ ((q*2^(s*n):ℕ):ℝ))
    push_cast at hh ⊢
    nlinarith only [hh]
  have hpow : (2:ℝ)^(s*n)*((2^(d*n):ℕ):ℝ)^4 = (2:ℝ)^((s+4*d)*n) := by
    push_cast
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  apply (div_le_iff₀ (by positivity : 0<4*((2^(8*k*n):ℕ):ℝ))).mpr
  have he : 10*(q:ℝ)*(2:ℝ)^((s+4*d)*n)/(2:ℝ)^(8*k*n)*
      (4*((2^(8*k*n):ℕ):ℝ)) = 40*(q:ℝ)*(2:ℝ)^((s+4*d)*n) := by push_cast; field_simp; ring
  rw [he,←hpow]
  nlinarith only [h₁,h₂,mul_nonneg (by positivity : 0≤(q:ℝ)*(2:ℝ)^(s*n))
    (by positivity : 0≤((2^(d*n):ℕ):ℝ)^4)]

end OrdinarySparsePowerScales

end

end OAI
