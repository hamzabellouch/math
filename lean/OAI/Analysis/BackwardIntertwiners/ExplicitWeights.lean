import OAI.Analysis.BackwardIntertwiners.FiberTails

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section


def weightBlock (k : ℕ) : ℕ := Nat.log 8 k + 1
def residueScale (k : ℕ) : ℕ := 2 ^ weightBlock k

def residueCorrection (t : ℕ → ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else 100 * ((residueScale k : ℝ) - 2 + t (weightBlock k))
def halfExponent (t : ℕ → ℕ) (k : ℕ) : ℝ :=
  10 * ((k : ℝ) + 1) + residueCorrection t k

def ResidueBounds (t : ℕ → ℕ) : Prop := ∀ m, t m < 2 ^ m

lemma residueScale_ge_two (k : ℕ) : 2 ≤ residueScale k := by
  dsimp [residueScale, weightBlock]
  simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ Nat.log 8 k + 1))

lemma residueCorrection_nonneg (t : ℕ → ℕ) (k : ℕ) : 0 ≤ residueCorrection t k := by
  dsimp [residueCorrection]
  split_ifs
  · rfl
  · have hh : (2:ℝ) ≤ residueScale k := by exact_mod_cast residueScale_ge_two k
    positivity

lemma residueCorrection_le {t : ℕ → ℕ} (ht : ResidueBounds t) (k : ℕ) :
    residueCorrection t k ≤ 200 * residueScale k := by
  have hN : (0:ℝ) ≤ residueScale k := Nat.cast_nonneg _
  dsimp [residueCorrection]
  split_ifs
  · positivity
  · have hr : (t (weightBlock k):ℝ) < residueScale k := by exact_mod_cast ht (weightBlock k)
    linarith

lemma residueCorrection_mono {t : ℕ → ℕ} (ht : ResidueBounds t) :
    Monotone (residueCorrection t) := by
  intro k l hkl
  by_cases hk : k = 0
  · simpa [hk, residueCorrection] using residueCorrection_nonneg t l
  have hl : l ≠ 0 := by omega
  have hq : weightBlock k ≤ weightBlock l := Nat.add_le_add_right (Nat.log_mono_right hkl) 1
  dsimp only [residueCorrection]
  rw [ite_eq_right hk, ite_eq_right hl]
  rcases hq.eq_or_lt with hq | hq
  · simp [hq, residueScale]
  · have hNN : 2 * residueScale k ≤ residueScale l := by
      dsimp [residueScale]
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNk : (2 * residueScale k : ℝ) ≤ residueScale l := by exact_mod_cast hNN
    have htk : (t (weightBlock k) : ℝ) < residueScale k := by exact_mod_cast ht _
    have htl : (0:ℝ) ≤ t (weightBlock l) := Nat.cast_nonneg _
    linarith

lemma halfExponent_mono {t : ℕ → ℕ} (ht : ResidueBounds t) : Monotone (halfExponent t) := by
  intro k l hkl
  have hc := residueCorrection_mono ht hkl
  have hkl' : (k:ℝ) ≤ l := by exact_mod_cast hkl
  dsimp [halfExponent]
  linarith

lemma halfExponent_lower (t : ℕ → ℕ) (k : ℕ) :
    10*((k:ℝ)+1) ≤ halfExponent t k := by
  have hh := residueCorrection_nonneg t k
  dsimp [halfExponent]
  linarith

@[simp] lemma halfExponent_zero (t : ℕ → ℕ) : halfExponent t 0 = 10 := by
  norm_num [halfExponent, residueCorrection]

lemma residueScale_sq_le {k : ℕ} (hk : k ≠ 0) : (residueScale k)^2 ≤ 4*k := by
  let q := Nat.log 8 k
  have hq : 8 ^ q ≤ k := Nat.pow_log_le_self 8 hk
  have h4 : 4 ^ q ≤ 8 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have he : (residueScale k)^2 = 4 * 4 ^ q := by
    change (2 ^ (q+1))^2 = 4 * 4^q
    rw [pow_succ (2:ℕ) q, mul_pow, ← pow_mul, mul_comm q 2, pow_mul]
    norm_num
    ring
  rw [he]
  omega

lemma residueCorrection_sqrt_bound {t : ℕ → ℕ} (ht : ResidueBounds t) (k : ℕ) :
    residueCorrection t k ≤ 400 * Real.sqrt k := by
  by_cases hk : k = 0
  · simp [hk, residueCorrection]
  have hs : (residueScale k : ℝ)^2 ≤ 4*(k:ℝ) := by exact_mod_cast residueScale_sq_le hk
  have hroot := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hroot0 := Real.sqrt_nonneg (k:ℝ)
  have hN0 : (0:ℝ) ≤ residueScale k := Nat.cast_nonneg _
  have hNr : (residueScale k : ℝ) ≤ 2*Real.sqrt k := by nlinarith
  exact (residueCorrection_le ht k).trans (by linarith)

def halfSum (t : ℕ → ℕ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, halfExponent t k

@[simp] lemma halfSum_zero (t : ℕ → ℕ) : halfSum t 0 = 0 := by simp [halfSum]
@[simp] lemma halfSum_succ (t : ℕ → ℕ) (n : ℕ) :
    halfSum t (n+1) = halfSum t n + halfExponent t n := by simp [halfSum, Finset.sum_range_succ]

lemma halfSum_linear (n : ℕ) :
    (∑ k ∈ Finset.range n, (10:ℝ)*((k:ℝ)+1)) = 5*(n:ℝ)*((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma halfSum_bounds {t : ℕ → ℕ} (ht : ResidueBounds t) (n : ℕ) :
    5*(n:ℝ)*((n:ℝ)+1) ≤ halfSum t n ∧
    halfSum t n ≤ 5*(n:ℝ)*((n:ℝ)+1) + 400*(n:ℝ)*Real.sqrt n := by
  have he : halfSum t n = 5*(n:ℝ)*((n:ℝ)+1) +
      ∑ k ∈ Finset.range n, residueCorrection t k := by
    simp only [halfSum, halfExponent, Finset.sum_add_distrib, halfSum_linear]
  rw [he]
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => residueCorrection_nonneg t k))
  · have hh : (∑ k ∈ Finset.range n, residueCorrection t k) ≤
        ∑ _k ∈ Finset.range n, 400*Real.sqrt n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : (k:ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
      exact (residueCorrection_sqrt_bound ht k).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkn) (by norm_num))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    nlinarith

lemma halfSum_quadratic {t : ℕ → ℕ} (ht : ResidueBounds t) :
    Tendsto (fun n : ℕ => halfSum t n / (n:ℝ)^2) atTop (𝓝 5) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hz : Tendsto (fun n : ℕ => halfSum t n / (n:ℝ)^2 - 5) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 5*(n:ℝ)⁻¹ + 400*(Real.sqrt (n:ℝ))⁻¹) ?_ ?_
      (by simpa using (hi.const_mul 5).add (hs.const_mul 400))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hh := (halfSum_bounds ht n).1
      have hdiv := (le_div_iff₀ (sq_pos_of_pos hn0)).mpr (show 5*(n:ℝ)^2 ≤ halfSum t n by nlinarith)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hr0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
      have hr := Real.sq_sqrt hn0.le
      have hh := (halfSum_bounds ht n).2
      have he : (5*(n:ℝ)*((n:ℝ)+1) + 400*(n:ℝ)*Real.sqrt n) / (n:ℝ)^2 - 5 =
          5*(n:ℝ)⁻¹ + 400*(Real.sqrt (n:ℝ))⁻¹ := by
        field_simp
        nlinarith
      rw [← he]
      exact sub_le_sub_right (div_le_div_of_nonneg_right hh (sq_nonneg _)) 5
  simpa only [sub_add_cancel, zero_add] using hz.add_const 5


def bilateralExponent (t u : ℕ → ℕ) : ℤ → ℝ
  | .ofNat n => halfExponent t n
  | .negSucc n => halfExponent u n

def bilateralBeta (t u : ℕ → ℕ) (j : ℤ) : ℝ := Real.exp (-bilateralExponent t u j)


def bilateralWeight (t u : ℕ → ℕ) : ℤ → ℝ
  | .ofNat n => Real.exp (-halfSum t n)
  | .negSucc n => Real.exp (halfSum u (n+1))

@[simp] lemma bilateralWeight_nat (t u : ℕ → ℕ) (n : ℕ) :
    bilateralWeight t u n = Real.exp (-halfSum t n) := rfl
@[simp] lemma bilateralWeight_neg_nat (t u : ℕ → ℕ) (n : ℕ) :
    bilateralWeight t u (-(n:ℤ)) = Real.exp (halfSum u n) := by
  cases n with
  | zero => simp [bilateralWeight]
  | succ n => rfl

lemma bilateralExponent_nonneg (t u : ℕ → ℕ) (j : ℤ) : 10 ≤ bilateralExponent t u j := by
  cases j with
  | ofNat n =>
    have hh := halfExponent_lower t n
    change 10 ≤ halfExponent t n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  | negSucc n =>
    have hh := halfExponent_lower u n
    change 10 ≤ halfExponent u n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    linarith

lemma bilateralWeight_pos (t u : ℕ → ℕ) (j : ℤ) : 0 < bilateralWeight t u j := by
  cases j <;> exact Real.exp_pos _

lemma bilateralWeight_ratio (t u : ℕ → ℕ) (j : ℤ) :
    bilateralWeight t u (j+1) / bilateralWeight t u j = bilateralBeta t u j := by
  cases j with
  | ofNat n =>
    change Real.exp (-halfSum t (n+1)) / Real.exp (-halfSum t n) = Real.exp (-halfExponent t n)
    rw [← Real.exp_sub, halfSum_succ]
    congr 1
    ring
  | negSucc n =>
    cases n with
    | zero =>
      change Real.exp (-halfSum t 0) / Real.exp (halfSum u 1) = Real.exp (-halfExponent u 0)
      simp [halfSum_succ, Real.exp_neg]
    | succ n =>
      change Real.exp (halfSum u (n+1)) / Real.exp (halfSum u (n+1+1)) = Real.exp (-halfExponent u (n+1))
      rw [← Real.exp_sub, halfSum_succ u (n+1)]
      congr 1
      ring

lemma bilateralWeight_antitone (t u : ℕ → ℕ) : Antitone (bilateralWeight t u) := by
  apply antitone_int_of_succ_le
  intro j
  have hr := bilateralWeight_ratio t u j
  have he : bilateralBeta t u j ≤ 1 := by
    rw [bilateralBeta, Real.exp_le_one_iff]
    have hh := bilateralExponent_nonneg t u j
    linarith
  exact (div_le_one (bilateralWeight_pos t u j)).mp (hr.le.trans he)

lemma halfSum_discreteConvex {t : ℕ → ℕ} (ht : ResidueBounds t) : DiscreteConvex (halfSum t) := by
  unfold DiscreteConvex
  simpa only [halfSum_succ, add_sub_cancel_left] using halfExponent_mono ht

lemma halfSum_root_bound {t : ℕ → ℕ} (ht : ResidueBounds t) {n : ℕ} (hn : 0 < n) :
    -halfSum t n / (n:ℝ) ≤ -5*(n:ℝ) := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hn').mpr
  have hh := (halfSum_bounds ht n).1
  nlinarith

lemma bilateralWeight_roots_summable {t u : ℕ → ℕ} (ht : ResidueBounds t) (hu : ResidueBounds u) :
    Summable (fun j : ℤ => if j = 0 then (0:ℝ) else bilateralWeight t u j ^ (1/(j:ℝ))) := by
  have hs : Summable (fun n : ℕ => Real.exp (-5*(n:ℝ))) := by
    simpa only [mul_comm (-5:ℝ)] using Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-5:ℝ) < 0)
  apply Summable.of_nat_of_neg_add_one
  · apply hs.of_nonneg_of_le
    · intro n
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (bilateralWeight_pos t u _).le _
    · intro n
      by_cases hn : n = 0
      · simp [hn]
      · rw [ite_eq_right (by exact_mod_cast hn), bilateralWeight_nat, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div, Int.cast_natCast] using halfSum_root_bound ht (Nat.pos_of_ne_zero hn)
  · have hs' : Summable (fun n : ℕ => Real.exp (-5*((n:ℝ)+1))) := by
      simpa only [mul_add, mul_one, Real.exp_add] using hs.mul_right (Real.exp (-5))
    apply hs'.of_nonneg_of_le
    · intro n
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (bilateralWeight_pos t u _).le _
    · intro n
      have hj : -((n:ℤ)+1) = -((n+1:ℕ):ℤ) := by omega
      rw [hj, ite_eq_right (by omega), bilateralWeight_neg_nat, ← Real.exp_mul]
      apply Real.exp_le_exp.mpr
      have hb := halfSum_root_bound hu (Nat.zero_lt_succ n)
      convert hb using 1 <;>
        simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.succ_eq_add_one, inv_neg,
          div_eq_mul_inv, Nat.cast_add, Nat.cast_one] ; ring

lemma bilateralWeight_quadratic {t u : ℕ → ℕ} (ht : ResidueBounds t) (hu : ResidueBounds u) :
    QuadraticWeights (bilateralWeight t u) where
  positive := bilateralWeight_pos t u
  decreasing := bilateralWeight_antitone t u
  convex_negative := by
    simpa only [bilateralWeight_neg_nat, Real.log_exp] using halfSum_discreteConvex hu
  concave_positive := by
    simpa only [bilateralWeight_nat, Real.log_exp, neg_neg] using halfSum_discreteConvex ht
  root_sum := bilateralWeight_roots_summable ht hu
  quadratic := by
    refine ⟨5, ?_, ?_, ?_⟩
    · exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num : (3:ℝ) ≠ 1)).trans (by norm_num)
    · simpa only [bilateralWeight_nat, Real.log_exp, neg_div] using (halfSum_quadratic ht).neg
    · simpa only [bilateralWeight_neg_nat, Real.log_exp] using halfSum_quadratic hu


end
end BackwardIntertwiners

end OAI
