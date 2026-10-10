import OAI.NumberTheory.TotientAsymptotic.NormalPrimeBands

namespace OAI

/-! Integer size and large-prime-part bounds for Ford's comparison hypotheses. -/

noncomputable section

namespace TotientAsymptotic

def partBelow (n : ℕ) (Z : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)).prod

lemma partBelow_mul_partAbove {n : ℕ} (hn : n ≠ 0) (Z : ℝ) :
    partBelow n Z*partAbove n Z=n := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p : ℝ) ≤ Z) id n.primeFactorsList
  simpa only [partBelow,partAbove,List.map_id,not_le,Nat.prod_primeFactorsList hn] using hh

lemma partBelow_bound (n : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (partBelow n Z : ℝ) ≤ Z^n.primeFactorsList.length := by
  let l := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)
  have hb (l : List ℕ) (hl : ∀ p ∈ l, (p : ℝ) ≤ Z) :
      (l.map (fun p : ℕ => (p : ℝ))).prod ≤ Z^l.length := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hp := hl p (by simp)
      have ht := ih (fun q hq => hl q (by simp [hq]))
      have hn : 0 ≤ (l.map (fun p : ℕ => (p : ℝ))).prod :=
        List.prod_nonneg (by simp)
      simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using
        mul_le_mul hp ht hn (zero_le_one.trans hZ)
  have hp : ((l.map (fun p : ℕ => (p : ℝ))).prod) ≤ Z^l.length := by
    apply hb
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  have hc : (partBelow n Z : ℝ)=(l.map (fun p : ℕ => (p : ℝ))).prod := by
    exact Nat.cast_list_prod l
  rw [hc]
  exact hp.trans (pow_le_pow_right₀ hZ (List.length_filter_le _ _))

lemma smooth_integer_log_bound {n : ℕ} {Z K : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hs : (largestPrimeFactor n : ℝ) ≤ Z) (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    Real.log (n : ℝ) ≤ K*Real.log Z := by
  have hp : (n : ℝ) ≤ Z^n.primeFactorsList.length := by
    have he : (n : ℝ) ≤ (largestPrimeFactor n : ℝ)^n.primeFactorsList.length := by
      exact_mod_cast self_le_largest_pow_length hn.ne'
    exact he.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hs _)
  have hl := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n) hp
  rw [Real.log_pow] at hl
  exact hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hZ))

lemma smooth_integer_size {n : ℕ} {Z K y ε : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hs : (largestPrimeFactor n : ℝ) ≤ Z) (hΩ : (n.primeFactorsList.length : ℝ) ≤ K)
    (hy : 0 < y) (hsize : K*Real.log Z ≤ ε*Real.log y) :
    (n : ℝ) ≤ y^ε := by
  have hl := (smooth_integer_log_bound hn hZ hs hΩ).trans hsize
  rw [Real.rpow_def_of_pos hy]
  apply (Real.log_le_iff_le_exp (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  simpa only [mul_comm] using hl

lemma partAbove_log_lower {n : ℕ} {Z K : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    Real.log (n : ℝ)-K*Real.log Z ≤ Real.log (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have hb : 0 < partBelow n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have hl := Real.log_le_log (by exact_mod_cast hb : (0 : ℝ) < partBelow n Z)
    (partBelow_bound n hZ)
  rw [Real.log_pow] at hl
  have hk := mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hZ)
  have he' := congrArg (fun z : ℕ => Real.log (z : ℝ)) he
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne') (by exact_mod_cast ha.ne')] at he'
  linarith

lemma partAbove_gt_sqrt {n : ℕ} {Z K y : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) (hy : 0 < y)
    (hsize : Real.log y/2 < Real.log (n : ℝ)-K*Real.log Z) :
    Real.sqrt y < (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  apply (Real.log_lt_log_iff (Real.sqrt_pos.mpr hy) (by exact_mod_cast ha)).mp
  rw [Real.log_sqrt hy.le]
  exact hsize.trans_le (partAbove_log_lower hn hZ hΩ)

end TotientAsymptotic

end

end OAI
