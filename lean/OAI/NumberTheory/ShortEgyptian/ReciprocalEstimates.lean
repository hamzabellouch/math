import OAI.NumberTheory.ShortEgyptian.IteratedDifferencing

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocal_leaf_sqrt (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    (Z U : ℝ) (p q : ℤ) (hZ : 0 ≤ Z) (hU : 1 ≤ U)
    (hp : U ≤ p) (hq : (q : ℝ) + hs.sum ≤ 2 * U) (hpq : p ≤ q)
    (lam : ℝ) (hlamdef : lam =
      Z * (hs.prod * (hs.length + 2).factorial * (1 / (3 * U)) ^ (hs.length + 3)))
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ‖∑ n ∈ Icc p q, phase (backwardDifferences hs (fun x => Z / x) n)‖ ≤
      6 * (3 : ℝ) ^ (hs.length + 3) * U * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by
  have hU0 : 0 < U := by linarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hfun : (fun x : ℝ => Z / x) = (fun x => Z * (1 / x)) := by
    ext x; ring
  have hstep (n : ℤ) (hn : n ∈ Ico p q) :
      lam ≤ (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) ∧
      (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) ≤
        (3 : ℝ) ^ (hs.length + 3) * lam := by
    have hn' := mem_Ico.mp hn
    have hnU : U ≤ (n : ℝ) := hp.trans (by exact_mod_cast hn'.1)
    have hnq : (n : ℝ) + 1 ≤ q := by exact_mod_cast hn'.2
    have hxV : (n : ℝ) + (1 :: 1 :: hs).sum ≤ 3 * U := by
      simp only [List.sum_cons]
      linarith
    have hb := backwardDifferences_reciprocal_bounds (1 :: 1 :: hs) (by
      intro h hh
      simp only [List.mem_cons] at hh
      rcases hh with rfl | rfl | hh
      · norm_num
      · norm_num
      · exact hhs h hh) hU0 hnU hxV
    simp only [List.prod_cons, one_mul, List.length_cons] at hb
    have hlen2 : hs.length + 1 + 1 = hs.length + 2 := by omega
    have hlen3 : hs.length + 1 + 1 + 1 = hs.length + 3 := by omega
    rw [hlen2, hlen3] at hb
    have hd : (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) =
        Z * backwardDifferences (1 :: 1 :: hs) (fun x => 1 / x) n := by
      rw [hfun]
      simp only [backwardDifferences_smul, backwardDifferences]
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      ring
    rw [hd, hlamdef]
    constructor
    · exact mul_le_mul_of_nonneg_left hb.1 hZ
    · have hident : (1 / U) ^ (hs.length + 3) =
          (3 : ℝ) ^ (hs.length + 3) * (1 / (3 * U)) ^ (hs.length + 3) := by
        rw [← mul_pow]
        congr 1
        field_simp
      have hh := mul_le_mul_of_nonneg_left hb.2 hZ
      rw [hident] at hh
      have heq : Z * (hs.prod * ↑(hs.length + 2).factorial *
          (3 ^ (hs.length + 3) * (1 / (3 * U)) ^ (hs.length + 3))) =
          3 ^ (hs.length + 3) * (Z * (hs.prod * ↑(hs.length + 2).factorial *
          (1 / (3 * U)) ^ (hs.length + 3))) := by ring
      rw [heq] at hh
      exact hh
  have hh := phase_sum_second_derivative_int
    (fun n => backwardDifferences hs (fun x => Z / x) n) p q hpq
    hlam hlam1 (by positivity : (0 : ℝ) ≤ 3 ^ (hs.length + 3)) (by
      intro n hn
      simpa only [Int.cast_add, Int.cast_ofNat, Int.cast_one] using hstep n hn)
  have hlength : (q - p : ℤ) ≤ U := by
    push_cast
    linarith
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right hlength (show 0 ≤ 6 * (3 : ℝ) ^ (hs.length + 3) * Real.sqrt lam by positivity)
  nlinarith

theorem real_list_prod_le_pow (hs : List ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hhs : ∀ h ∈ hs, 0 ≤ h ∧ h ≤ L) : hs.prod ≤ L ^ hs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have hh := hhs h (by simp)
    have ht : ∀ x ∈ hs, 0 ≤ x ∧ x ≤ L := fun x hx => hhs x (by simp [hx])
    simp only [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hh.2 (ih ht) (List.prod_nonneg (fun x hx => (ht x hx).1)) hL

theorem reciprocal_phase_parameter_bound (r L : ℕ) (Z U eps : ℝ) (p q : ℤ)
    (hL : 1 ≤ L) (hU : 1 ≤ U) (hLU : (L : ℝ) ≤ 2 * U)
    (hZ : 0 ≤ Z) (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ r))
    (hconstant : 18 ≤ U * eps ^ (2 ^ r))
    (hlow : (18 / (U * eps ^ (2 ^ r))) ^ 2 ≤
      Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)))
    (hupp : (L : ℝ) ^ r *
      (Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))) ≤
      (eps ^ (2 ^ r) / (18 * (3 : ℝ) ^ (r + 3))) ^ 2) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U * eps := by
  classical
  have hU0 : 0 < U := by linarith
  have hsize : ((Icc p q).card : ℝ) ≤ 2 * U := by
    by_cases hpq : p ≤ q
    · rw [Int.card_Icc]
      have hcast : (((q + 1 - p).toNat : ℕ) : ℝ) = (q + 1 - p : ℤ) := by
        exact_mod_cast (show ((q + 1 - p).toNat : ℤ) = q + 1 - p by omega)
      rw [hcast]
      push_cast
      linarith
    · rw [Icc_eq_empty_of_lt (by omega : q < p), card_empty, Nat.cast_zero]
      positivity
  have hh := iterated_interval_vdc r (fun x => Z / x) p q L (2 * U) eps
    hL (by positivity) hLU hsize heps.le heps1 hLin (by
      intro hs hlen hhs
      let vs : List ℝ := hs.map (fun h : ℤ => (h : ℝ))
      have hvlen : vs.length = r := by simpa only [vs, List.length_map] using hlen
      have hvs : ∀ h ∈ vs, 1 ≤ h ∧ h ≤ (L : ℝ) := by
        intro h hh
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
        obtain ⟨ha0, haL⟩ := hhs a ha
        exact ⟨by exact_mod_cast ha0, by exact_mod_cast haL.le⟩
      have hp1 : 1 ≤ vs.prod := List.one_le_prod (fun h hh => (hvs h hh).1)
      have hpL : vs.prod ≤ (L : ℝ) ^ r := by
        have hp' := real_list_prod_le_pow vs (by positivity : (0 : ℝ) ≤ L)
          (fun h hh => ⟨le_trans (by norm_num) (hvs h hh).1, (hvs h hh).2⟩)
        simpa only [hvlen] using hp'
      have hvsum : vs.sum = (hs.sum : ℝ) := by simp [vs]
      by_cases hne : p ≤ q - hs.sum
      · let c : ℝ := Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))
        let lam : ℝ := vs.prod * c
        let A : ℝ := (3 : ℝ) ^ (r + 3)
        let d : ℝ := eps ^ (2 ^ r)
        have hd : 0 < d := by dsimp [d]; positivity
        have hd1 : d ≤ 1 := pow_le_one₀ heps.le heps1
        have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
        have hc : 0 < c := lt_of_lt_of_le (by positivity) hlow
        have hlo : (18 / (U * d)) ^ 2 ≤ lam := by
          apply hlow.trans
          dsimp only [lam]
          nlinarith
        have hup : lam ≤ (d / (18 * A)) ^ 2 :=
          (mul_le_mul_of_nonneg_right hpL hc.le).trans hupp
        have hlu : lam ≤ 1 := by
          have hfrac : d / (18 * A) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
          exact hup.trans (pow_le_one₀ (by positivity) hfrac)
        have hlpos : 0 < lam := lt_of_lt_of_le (by positivity) hlo
        have hslo : 18 / (U * d) ≤ Real.sqrt lam :=
          (Real.le_sqrt (by positivity) hlpos.le).mpr hlo
        have hsup : Real.sqrt lam ≤ d / (18 * A) :=
          (Real.sqrt_le_left (by positivity)).mpr hup
        have hlamdef : lam = Z * (vs.prod * (vs.length + 2).factorial *
            (1 / (3 * U)) ^ (vs.length + 3)) := by
          dsimp only [lam, c]
          rw [hvlen]
          ring
        have hlast := reciprocal_leaf_sqrt vs (fun h hh => le_trans (by norm_num) (hvs h hh).1)
          Z U p (q - hs.sum) hZ hU hp (by rw [hvsum]; push_cast; linarith)
          hne lam hlamdef hlpos hlu
        have hs1 : 6 * A * U * Real.sqrt lam ≤ U * d / 3 := by
          have hh1 := (le_div_iff₀ (show 0 < 18 * A by positivity)).mp hsup
          have hh2 := mul_le_mul_of_nonneg_left hh1 hU0.le
          nlinarith
        have hs2 : 6 / Real.sqrt lam ≤ U * d / 3 := by
          apply (div_le_iff₀ (Real.sqrt_pos.mpr hlpos)).mpr
          have hh1 := (div_le_iff₀ (show 0 < U * d by positivity)).mp hslo
          nlinarith
        have hs3 : 6 ≤ U * d / 3 := by dsimp only [d]; linarith
        rw [hvlen] at hlast
        change ‖∑ n ∈ Icc p (q - hs.sum),
          phase (backwardDifferences vs (fun x => Z / x) n)‖ ≤ _
        change ‖∑ n ∈ Icc p (q - hs.sum),
          phase (backwardDifferences vs (fun x => Z / x) n)‖ ≤ 6 * A * U * Real.sqrt lam + 6 / Real.sqrt lam + 6 at hlast
        change _ ≤ 2 * U * d
        nlinarith
      · rw [Icc_eq_empty_of_lt (by omega : q - hs.sum < p), sum_empty, norm_zero]
        positivity)
  convert hh using 1
  ring

end ShortEgyptian

end OAI
