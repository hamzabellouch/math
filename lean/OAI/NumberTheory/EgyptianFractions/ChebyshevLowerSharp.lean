import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators
open Finset Filter Asymptotics
open ArithmeticFunction

namespace Problem337.ChebyshevLowerSharp

/-- Chebyshev's periodic floor kernel takes only the values zero and one. -/
lemma floor_kernel_bounds (n : ℕ) :
    n / 2 + n / 3 + n / 5 ≤ n + n / 30 ∧
      n + n / 30 ≤ 1 + n / 2 + n / 3 + n / 5 := by
  omega

lemma log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih,
      ← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le n)]
    simp [Finset.sum_insert]

/-- A finite summatory von Mangoldt identity, including the floor weights. -/
lemma log_factorial_eq_mangoldt_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Ioc 0 n, (n / d : ℕ) * vonMangoldt d := by
  classical
  rw [log_factorial_eq_sum_log]
  have hdiv (k : ℕ) (hk : k ∈ Ioc 0 n) :
      k.divisors = (Ioc 0 n).filter (fun d => d ∣ k) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, hk0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Finset.mem_Ioc.mp hk).1,
        (Nat.le_of_dvd (Finset.mem_Ioc.mp hk).1 hd).trans
          (Finset.mem_Ioc.mp hk).2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, (Finset.mem_Ioc.mp hk).1.ne'⟩
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ d ∈ Ioc 0 n,
        if d ∣ k then vonMangoldt d else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← ArithmeticFunction.vonMangoldt_sum, hdiv k hk, Finset.sum_filter]
    _ = ∑ d ∈ Ioc 0 n, ∑ k ∈ Ioc 0 n,
        if d ∣ k then vonMangoldt d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Nat.Ioc_filter_dvd_card_eq_div]

/-- The summatory identity may be extended to any larger finite interval. -/
lemma log_factorial_eq_mangoldt_sum_of_le {n N : ℕ} (hnN : n ≤ N) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Ioc 0 N, (n / d : ℕ) * vonMangoldt d := by
  rw [log_factorial_eq_mangoldt_sum]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right hnN)
  intro d hd hdn
  have hnd : n < d := by
    simp only [Finset.mem_Ioc] at hd hdn
    omega
  simp [Nat.div_eq_of_lt hnd]

/-- A finite stronger Chebyshev lower bound. The alternating factorial
combination is bounded above by the actual von Mangoldt summatory function. -/
theorem factorial_combination_le_psi (N : ℕ) :
    Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
      Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
      Real.log ((N / 30).factorial : ℝ) ≤ Chebyshev.psi N := by
  rw [log_factorial_eq_mangoldt_sum,
    log_factorial_eq_mangoldt_sum_of_le (Nat.div_le_self N 2),
    log_factorial_eq_mangoldt_sum_of_le (Nat.div_le_self N 3),
    log_factorial_eq_mangoldt_sum_of_le (Nat.div_le_self N 5),
    log_factorial_eq_mangoldt_sum_of_le (Nat.div_le_self N 30)]
  simp only [Chebyshev.psi, Nat.floor_natCast, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hkernel := (floor_kernel_bounds (N / d)).2
  have hdiv (a : ℕ) : N / a / d = (N / d) / a := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hreal : ((N / d : ℕ) : ℝ) + ((N / d / 30 : ℕ) : ℝ) ≤
      1 + ((N / d / 2 : ℕ) : ℝ) + ((N / d / 3 : ℕ) : ℝ) +
        ((N / d / 5 : ℕ) : ℝ) := by exact_mod_cast hkernel
  rw [hdiv 2, hdiv 3, hdiv 5, hdiv 30]
  have hm := mul_le_mul_of_nonneg_right hreal (vonMangoldt_nonneg (n := d))
  nlinarith

/-- The linear-scale error in the logarithmic factorial estimate vanishes. -/
lemma log_factorial_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log n + n) / n)
      atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
    (by positivity : Real.sqrt Real.pi ≠ 0)).div_atTop hnat
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hc := hnat.const_div_atTop (Real.log 2)
  have hlim := hs.add ((hc.add hl).div_const 2)
  simp only [zero_add, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hf := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR,
    Real.log_div hnR (Real.exp_ne_zero 1), Real.log_exp] at hf
  dsimp only [Function.comp_def, id_eq]
  rw [hf]
  ring

/-- A scaled version with the common divergent logarithm subtracted. -/
lemma scaled_log_factorial_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      Real.log ((a * n).factorial : ℝ) / n - (a : ℝ) * Real.log n)
      atTop (nhds ((a : ℝ) * Real.log a - a)) := by
  have hmul : Tendsto (fun n : ℕ => a * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n ha) tendsto_id
  have hlim := ((log_factorial_error_tendsto_zero.comp hmul).mul_const (a : ℝ)).add_const
    ((a : ℝ) * Real.log a - a)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp_def, Nat.cast_mul]
  rw [Real.log_mul haR hnR]
  field_simp
  ring

/-- Chebyshev's classical elementary lower constant, approximately `0.92129`. -/
def lowerConstant : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

lemma lowerConstant_eq :
    lowerConstant = (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30 := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [lowerConstant, h30]
  ring

lemma lowerConstant_gt_921_div_1000 : (921 / 1000 : ℝ) < lowerConstant := by
  have h5 := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 1
  norm_num at h5
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0), h4] at h5
  rw [lowerConstant_eq]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

def factorialBlock (n : ℕ) : ℝ :=
  Real.log ((30 * n).factorial : ℝ) - Real.log ((15 * n).factorial : ℝ) -
    Real.log ((10 * n).factorial : ℝ) - Real.log ((6 * n).factorial : ℝ) +
    Real.log (n.factorial : ℝ)

lemma factorialBlock_le_psi (n : ℕ) : factorialBlock n ≤ Chebyshev.psi (30 * n) := by
  have h := factorial_combination_le_psi (30 * n)
  have h2 : 30 * n / 2 = 15 * n := by omega
  have h3 : 30 * n / 3 = 10 * n := by omega
  have h5 : 30 * n / 5 = 6 * n := by omega
  have h30 : 30 * n / 30 = n := by omega
  simpa only [h2, h3, h5, h30, Nat.cast_mul, Nat.cast_ofNat, factorialBlock] using h

lemma factorialBlock_tendsto :
    Tendsto (fun n : ℕ => factorialBlock n / (30 * n)) atTop (nhds lowerConstant) := by
  have hlim := (((((scaled_log_factorial_tendsto 30 (by norm_num)).sub
    (scaled_log_factorial_tendsto 15 (by norm_num))).sub
    (scaled_log_factorial_tendsto 10 (by norm_num))).sub
    (scaled_log_factorial_tendsto 6 (by norm_num))).add
    (scaled_log_factorial_tendsto 1 (by norm_num))).div_const 30
  have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  convert hlim using 1
  · funext n
    simp only [factorialBlock, Nat.cast_ofNat, Nat.cast_one, Nat.one_mul]
    ring
  · rw [lowerConstant_eq]
    norm_num only [Nat.cast_ofNat, Nat.cast_one, Real.log_one, mul_zero,
      h15, h10, h6, h30]
    congr 1
    ring

/-- Rescaling the `30`-blocks loses only a bounded endpoint discrepancy. -/
lemma factorialBlock_div_tendsto :
    Tendsto (fun N : ℕ => factorialBlock (N / 30) / N)
      atTop (nhds lowerConstant) := by
  have hquot : Tendsto (fun N : ℕ => N / 30) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (30 * b)] with N hN
    omega
  have hratio : Tendsto (fun N : ℕ => (30 : ℝ) * (N / 30 : ℕ) / N)
      atTop (nhds 1) := by
    have h := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).sub
      (tendsto_mod_div_atTop_nhds_zero_nat (m := 30) (by norm_num))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have heq : ((N % 30 : ℕ) : ℝ) + 30 * ((N / 30 : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N 30
    field_simp
    linarith
  have hlim := (factorialBlock_tendsto.comp hquot).mul hratio
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (30 : ℕ)] with N hN
  have hqR : ((N / 30 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < N / 30 := by omega
    exact_mod_cast this.ne'
  dsimp only [Function.comp_def]
  field_simp

/-- Every coefficient below the classical Chebyshev constant is an eventual
lower coefficient for the actual von Mangoldt summatory function. -/
theorem eventually_psi_lower {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ N : ℕ in atTop, c * N ≤ Chebyshev.psi N := by
  have he := factorialBlock_div_tendsto.eventually (lt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hfirst : c * N < factorialBlock (N / 30) :=
    (lt_div_iff₀ hNR).1 hN
  have hlast : Chebyshev.psi (30 * (N / 30 : ℕ)) ≤ Chebyshev.psi N := by
    apply Chebyshev.psi_mono
    exact_mod_cast (show 30 * (N / 30) ≤ N by omega)
  exact hfirst.le.trans ((factorialBlock_le_psi (N / 30)).trans hlast)

/-- An unconditional prime-count lower bound with every coefficient below
`0.92129...`; no prime number theorem is used. -/
theorem eventually_primeCounting_lower {c : ℝ} (hc : c < lowerConstant) :
    ∀ᶠ N : ℕ in atTop, c * N / Real.log N ≤ (Nat.primeCounting N : ℝ) := by
  filter_upwards [eventually_psi_lower hc, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  apply (div_le_iff₀ hlog).2
  exact hN.trans (Chebyshev.psi_le_primeCounting_mul_log N)

theorem eventually_primeCounting_lower_092 :
    ∀ᶠ N : ℕ in atTop,
      (92 / 100 : ℝ) * N / Real.log N ≤ (Nat.primeCounting N : ℝ) := by
  apply eventually_primeCounting_lower
  linarith [lowerConstant_gt_921_div_1000]

/-- The unblocked finite factorial expression. -/
def factorialCombination (N : ℕ) : ℝ :=
  Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
    Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
    Real.log ((N / 30).factorial : ℝ)

lemma log_factorial_gap {n N M : ℕ} (hnN : n ≤ N) (hNM : N ≤ M)
    (hM : 1 ≤ M) (hgap : N - n ≤ 30) :
    0 ≤ Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) ∧
      Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) ≤ 30 * Real.log M := by
  have hsum := Finset.sum_Ioc_consecutive (fun k : ℕ => Real.log (k : ℝ))
    (Nat.zero_le n) hnN
  have heq : Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) =
      ∑ k ∈ Ioc n N, Real.log (k : ℝ) := by
    rw [log_factorial_eq_sum_log, log_factorial_eq_sum_log]
    linarith
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ k by have := (Finset.mem_Ioc.mp hk).1; omega)
  · calc
      _ ≤ ∑ _k ∈ Ioc n N, Real.log (M : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Real.log_le_log
        · exact_mod_cast (show 0 < k by have := (Finset.mem_Ioc.mp hk).1; omega)
        · exact_mod_cast ((Finset.mem_Ioc.mp hk).2.trans hNM)
      _ = (N - n : ℕ) * Real.log M := by simp
      _ ≤ 30 * Real.log M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hgap
        · exact Real.log_nonneg (by exact_mod_cast hM)

/-- Passing from a multiple of thirty to an arbitrary endpoint costs only
a logarithmic error. -/
lemma factorialCombination_sub_block_abs_le {N : ℕ} (hN : 1 ≤ N) :
    |factorialCombination N - factorialBlock (N / 30)| ≤ 120 * Real.log N := by
  have h0 := log_factorial_gap (n := 30 * (N / 30)) (N := N) (M := N)
    (by omega) le_rfl hN (by omega)
  have h2 := log_factorial_gap (n := 15 * (N / 30)) (N := N / 2) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have h3 := log_factorial_gap (n := 10 * (N / 30)) (N := N / 3) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have h5 := log_factorial_gap (n := 6 * (N / 30)) (N := N / 5) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  dsimp only [factorialCombination, factorialBlock]
  constructor <;> linarith [h0.1, h0.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2]

/-- The full, unblocked factorial combination has the same sharp coefficient. -/
theorem factorialCombination_div_tendsto :
    Tendsto (fun N : ℕ => factorialCombination N / N)
      atTop (nhds lowerConstant) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim : Tendsto (fun N : ℕ => 120 * (Real.log N / N)) atTop (nhds 0) := by
    simpa using hlog.const_mul 120
  have herror : Tendsto (fun N : ℕ =>
      (factorialCombination N - factorialBlock (N / 30)) / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun N => ?_) hlim
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hnormN : ‖(N : ℝ)‖ = (N : ℝ) :=
        Real.norm_of_nonneg (Nat.cast_nonneg N)
      rw [norm_div, hnormN, Real.norm_eq_abs]
      calc
        _ ≤ (120 * Real.log (N : ℝ)) / N :=
          div_le_div_of_nonneg_right (factorialCombination_sub_block_abs_le hN)
            (Nat.cast_nonneg N)
        _ = 120 * (Real.log (N : ℝ) / N) := by ring
  convert herror.add factorialBlock_div_tendsto using 1
  · funext N
    ring
  · simp

end Problem337.ChebyshevLowerSharp

end

end OAI
