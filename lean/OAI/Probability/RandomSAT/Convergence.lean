import OAI.Probability.RandomSAT.CenterComparison

namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def balanceConstant (β : ℝ) : ℝ := (3 : ℝ)^β / ((3 / 2 : ℝ)^β - 1)

theorem balanceConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < balanceConstant β :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))

theorem balanced_power_potential {β a b q : ℝ} (hβ : 0 < β) (hb : 0 < b)
    (hq : 0 < q) (haq : q / 3 ≤ a) (hbq : b ≤ q / (3 / 2)) :
    a^(-β) ≤ balanceConstant β * (b^(-β) - q^(-β)) := by
  have hA := Real.rpow_le_rpow_of_nonpos (div_pos hq (by norm_num)) haq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    div_inv_eq_mul] at hA
  have hB := Real.rpow_le_rpow_of_nonpos hb hbq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 2), div_inv_eq_mul] at hB
  have hd : (3 / 2 : ℝ)^β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))
  have hf : balanceConstant β * ((3 / 2 : ℝ)^β - 1) = (3 : ℝ)^β := by
    exact div_mul_cancel₀ _ hd
  calc
    a^(-β) ≤ q^(-β) * (3 : ℝ)^β := hA
    _ = balanceConstant β * (q^(-β) * ((3 / 2 : ℝ)^β - 1)) := by rw [← hf]; ring
    _ ≤ balanceConstant β * (b^(-β) - q^(-β)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hB]) (balanceConstant_pos hβ).le

theorem balanced_blocks_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ q : ℕ, 1 ≤ q → ∀ r : ℕ, r ≤ q →
      u s - A * (s : ℝ)^(-β) -
        A * balanceConstant β * (s : ℝ)^(-β) * (1 - (q : ℝ)^(-β)) ≤ u (q * s + r) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq r hr
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    have hpow : 0 ≤ (s : ℝ)^(-β) := (Real.rpow_pos_of_pos hs' _).le
    have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) :=
      mul_nonneg (mul_nonneg hA (balanceConstant_pos hβ).le) hpow
    by_cases hq1 : q = 1
    · subst q
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with hr0 | hr1
      · subst r
        simp only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul, add_zero]
        exact sub_le_self _ (mul_nonneg hA hpow)
      · subst r
        simpa only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul] using hnext
    · have hq2 : 2 ≤ q := by omega
      let a := q / 2
      let b := q - a
      let r₁ := min r a
      let r₂ := r - r₁
      have ha : 1 ≤ a := by dsimp [a]; omega
      have hb : 1 ≤ b := by dsimp [b, a]; omega
      have haq : a < q := by dsimp [a]; omega
      have hbq : b < q := by dsimp [b, a]; omega
      have hab : a ≤ b := by dsimp [a, b]; omega
      have habq : a + b = q := by dsimp [b, a]; omega
      have hqa : q ≤ 3 * a := by dsimp [a]; omega
      have hbq' : 3 * b ≤ 2 * q := by dsimp [b, a]; omega
      have hr₁ : r₁ ≤ a := min_le_right r a
      have hr₂ : r₂ ≤ b := by dsimp [r₂, r₁, b]; omega
      have hrr : r₁ + r₂ = r := by dsimp [r₂, r₁]; omega
      have hiA := ih a haq ha r₁ hr₁
      have hiB := ih b hbq hb r₂ hr₂
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      have habpow : (b : ℝ)^(-β) ≤ (a : ℝ)^(-β) :=
        Real.rpow_le_rpow_of_nonpos ha' (by exact_mod_cast hab) (neg_nonpos.mpr hβ.le)
      have hchild : u s - A * (s : ℝ)^(-β) -
          A * balanceConstant β * (s : ℝ)^(-β) * (1 - (b : ℝ)^(-β)) ≤
          min (u (a * s + r₁)) (u (b * s + r₂)) := by
        apply le_min
        · have hh := mul_le_mul_of_nonneg_left habpow hcoef
          nlinarith
        · exact hiB
      have hsizeA : N ≤ a * s + r₁ := by nlinarith
      have hsizeB : N ≤ b * s + r₂ := by nlinarith
      have hsize : a * s ≤ min (a * s + r₁) (b * s + r₂) := by
        apply le_min <;> nlinarith
      have hminpos : (0 : ℝ) < (a : ℝ) * s := mul_pos ha' hs'
      have hminpow := Real.rpow_le_rpow_of_nonpos hminpos
        (show (a : ℝ) * s ≤ (min (a * s + r₁) (b * s + r₂) : ℝ) by exact_mod_cast hsize)
        (neg_nonpos.mpr hβ.le)
      rw [Real.mul_rpow ha'.le hs'.le] at hminpow
      have herr := mul_le_mul_of_nonneg_left hminpow hA
      have hpotential := balanced_power_potential hβ hb' hq'
        (show (q : ℝ) / 3 ≤ a by
          have hh : (q : ℝ) ≤ 3 * a := by exact_mod_cast hqa
          linarith)
        (show (b : ℝ) ≤ q / (3 / 2) by
          have hh : 3 * (b : ℝ) ≤ 2 * q := by exact_mod_cast hbq'
          linarith)
      have hpot := mul_le_mul_of_nonneg_left hpotential (mul_nonneg hA hpow)
      have hc := hadd (a * s + r₁) hsizeA (b * s + r₂) hsizeB
      have he : a * s + r₁ + (b * s + r₂) = q * s + r := by
        calc
          _ = (a + b) * s + (r₁ + r₂) := by ring
          _ = _ := by rw [habq, hrr]
      rw [he] at hc
      simp only [Nat.cast_add, Nat.cast_mul] at hc
      nlinarith

theorem balanced_tail_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ n ≥ s * s,
      u s - A * (1 + balanceConstant β) * (s : ℝ)^(-β) ≤ u n := by
  intro n hn
  have hq : s ≤ n / s := (Nat.le_div_iff_mul_le hs).mpr hn
  have hr : n % s ≤ n / s := (Nat.mod_lt n hs).le.trans hq
  have hb := balanced_blocks_bound u hA hβ hsN hs hadd hnext (n / s) (by omega) (n % s) hr
  rw [Nat.mul_comm (n / s) s, Nat.div_add_mod] at hb
  have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) * ((n / s : ℕ) : ℝ)^(-β) := by
    have hB := (balanceConstant_pos hβ).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith

theorem summable_min_convergence (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (hcompare : ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N, min (u r) (u s) - A * (min r s : ℝ)^(-β) ≤ u (r + s)) ∧
      (∀ s ≥ N, u s - A * (s : ℝ)^(-β) ≤ u (s + 1))) :
    Filter.Tendsto u Filter.atTop (nhds (Filter.limsup u Filter.atTop)) := by
  obtain ⟨N, hadd, hnext⟩ := hcompare
  let α := Filter.limsup u Filter.atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (α - a) / 3
    have hε : 0 < ε := by dsimp [ε, α]; linarith
    have ht := (tendsto_rpow_neg_atTop hβ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hcost : Filter.Tendsto (fun s : ℕ => A * (1 + balanceConstant β) * (s : ℝ)^(-β))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using ht.const_mul (A * (1 + balanceConstant β))
    have hsmall := hcost.eventually_lt_const hε
    have hhigh : ∃ᶠ s : ℕ in Filter.atTop, α - ε < u s :=
      Filter.frequently_lt_of_lt_limsup hLower.isCoboundedUnder_le (by change α - ε < α; linarith)
    have hgood : ∀ᶠ s : ℕ in Filter.atTop,
        N ≤ s ∧ 0 < s ∧ A * (1 + balanceConstant β) * (s : ℝ)^(-β) < ε := by
      filter_upwards [Filter.eventually_ge_atTop (max N 1), hsmall] with s hs he
      exact ⟨by omega, by omega, he⟩
    obtain ⟨s, hsHigh, hsN, hs, hsSmall⟩ := (hhigh.and_eventually hgood).exists
    have htail := balanced_tail_bound u hA hβ hsN hs hadd (hnext s hsN)
    filter_upwards [Filter.eventually_ge_atTop (s * s)] with n hn
    have hh := htail n hn
    dsimp [ε] at hsHigh hsSmall
    linarith
  · intro a ha
    exact Filter.eventually_lt_of_limsup_lt ha hUpper

end


end FixedClauseThreshold

end OAI
