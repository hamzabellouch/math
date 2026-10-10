import OAI.Analysis.LpDimension.ElectricalProjection

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uI uJ

namespace SubpolynomialLp

def powerDefect (p a b : ℝ) : ℝ :=
  |a+b|^p + |a-b|^p - 2*|a|^p - 2*|b|^p

lemma sq_rpow_half (p a : ℝ) : (a^2)^(p/2) = |a|^p := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

lemma strictly_superadditive_rpow {p a b : ℝ} (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) :
    a^p + b^p < (a+b)^p := by
  have hsum : 0 < a+b := add_pos ha hb
  have hta : 0 < a/(a+b) := div_pos ha hsum
  have htb : 0 < b/(a+b) := div_pos hb hsum
  have ht : a/(a+b) + b/(a+b) = 1 := by field_simp
  have h1 := (strictConvexOn_rpow hp).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) hta htb ht
  have h2 := (strictConvexOn_rpow hp).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) htb hta (by linarith)
  have he1 : b/(a+b) * (a+b) = b := by field_simp
  have he2 : a/(a+b) * (a+b) = a := by field_simp
  simp only [smul_eq_mul, Real.zero_rpow (by linarith : p ≠ 0), mul_zero,
    zero_add] at h1 h2
  rw [he1] at h1
  rw [he2] at h2
  nlinarith [show (a/(a+b) + b/(a+b)) * (a+b)^p = (a+b)^p by rw [ht, one_mul]]

lemma strictly_subadditive_rpow {p a b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : 0 < b) :
    (a+b)^p < a^p + b^p := by
  have hsum : 0 < a+b := add_pos ha hb
  have hta : 0 < a/(a+b) := div_pos ha hsum
  have htb : 0 < b/(a+b) := div_pos hb hsum
  have ht : a/(a+b) + b/(a+b) = 1 := by field_simp
  have h1 := (Real.strictConcaveOn_rpow hp hp1).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) hta htb ht
  have h2 := (Real.strictConcaveOn_rpow hp hp1).2 (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (show a+b ∈ Set.Ici 0 from hsum.le) (ne_of_lt hsum) htb hta (by linarith)
  have he1 : b/(a+b) * (a+b) = b := by field_simp
  have he2 : a/(a+b) * (a+b) = a := by field_simp
  simp only [smul_eq_mul, Real.zero_rpow hp.ne', mul_zero, zero_add] at h1 h2
  rw [he1] at h1
  rw [he2] at h2
  nlinarith [show (a/(a+b) + b/(a+b)) * (a+b)^p = (a+b)^p by rw [ht, one_mul]]

lemma powerDefect_pos {p a b : ℝ} (hp : 2 < p) (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < powerDefect p a b := by
  have hc := (convexOn_rpow (show 1 ≤ p/2 by linarith)).2
    (show (a+b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a-b))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have he : (1/2:ℝ) * (a+b)^2 + (1/2:ℝ) * (a-b)^2 = a^2+b^2 := by ring
  simp only [smul_eq_mul, he] at hc
  have hs := strictly_superadditive_rpow (show 1 < p/2 by linarith)
    (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
  simp only [sq_rpow_half] at hc hs
  unfold powerDefect
  linarith

lemma powerDefect_neg {p a b : ℝ} (hp : 0 < p) (hp2 : p < 2) (ha : a ≠ 0) (hb : b ≠ 0) :
    powerDefect p a b < 0 := by
  have hc := (Real.concaveOn_rpow (show 0 ≤ p/2 by linarith) (show p/2 ≤ 1 by linarith)).2
    (show (a+b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a+b)) (show (a-b)^(2:ℕ) ∈ Set.Ici (0:ℝ) from sq_nonneg (a-b))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have he : (1/2:ℝ) * (a+b)^2 + (1/2:ℝ) * (a-b)^2 = a^2+b^2 := by ring
  simp only [smul_eq_mul, he] at hc
  have hs := strictly_subadditive_rpow (show 0 < p/2 by linarith) (show p/2 < 1 by linarith)
    (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
  simp only [sq_rpow_half] at hc hs
  unfold powerDefect
  linarith

lemma powerDefect_eq_zero_iff {p a b : ℝ} (hp : 0 < p) (hp2 : p ≠ 2) :
    powerDefect p a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro hh
    by_contra hab
    push Not at hab
    rcases lt_or_gt_of_ne hp2 with hlt | hgt
    · linarith [powerDefect_neg hp hlt hab.1 hab.2]
    · linarith [powerDefect_pos hgt hab.1 hab.2]
  · rintro (rfl | rfl) <;> simp [powerDefect, Real.zero_rpow hp.ne'] <;> ring

def lpPower {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : ℝ := ∑ i, |x i|^p

lemma lpPower_disjointness {I : Type uI} [Fintype I] (p : ℝ) (hp : 0 < p) (hp2 : p ≠ 2)
    (u v : I → ℝ) :
    lpPower p (u+v) + lpPower p (u-v) = 2*lpPower p u + 2*lpPower p v ↔
      ∀ i, u i = 0 ∨ v i = 0 := by
  have he : lpPower p (u+v) + lpPower p (u-v) - 2*lpPower p u - 2*lpPower p v =
      ∑ i, powerDefect p (u i) (v i) := by
    simp only [lpPower, powerDefect, Pi.add_apply, Pi.sub_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hz (i : I) : powerDefect p (u i) (v i) = 0 ↔ u i = 0 ∨ v i = 0 :=
    powerDefect_eq_zero_iff hp hp2
  rw [← sub_eq_zero, ← sub_sub, he]
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · rw [Finset.sum_eq_zero_iff_of_nonpos]
    · simp only [Finset.mem_univ, true_implies, hz]
    · intro i _
      by_cases hi : u i = 0 ∨ v i = 0
      · exact (hz i).2 hi |>.le
      · push Not at hi
        exact (powerDefect_neg hp hlt hi.1 hi.2).le
  · rw [Finset.sum_eq_zero_iff_of_nonneg]
    · simp only [Finset.mem_univ, true_implies, hz]
    · intro i _
      by_cases hi : u i = 0 ∨ v i = 0
      · exact (hz i).2 hi |>.ge
      · push Not at hi
        exact (powerDefect_pos hgt hi.1 hi.2).le

lemma abs_midpoint_rpow_strict {p a b : ℝ} (hp : 1 < p) (hab : a ≠ b) :
    |(a+b)/2|^p < (|a|^p+|b|^p)/2 := by
  by_cases he : |a| = |b|
  · have hn : a = -b := (abs_eq_abs.mp he).resolve_left hab
    have hb : b ≠ 0 := by intro h; apply hab; simpa [h] using hn
    rw [hn]
    simp only [neg_add_cancel, zero_div, abs_zero, Real.zero_rpow (by linarith : p ≠ 0), abs_neg]
    positivity
  · have hh := (strictConvexOn_rpow hp).2 (abs_nonneg a) (abs_nonneg b) he
      (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    have hm : |(a+b)/2| ≤ (1/2:ℝ)*|a|+(1/2:ℝ)*|b| := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_add_le a b]
    have hr := Real.rpow_le_rpow (abs_nonneg ((a+b)/2)) hm (show 0 ≤ p by linarith)
    exact hr.trans_lt (by linarith [hh])

lemma abs_midpoint_rpow_le {p a b : ℝ} (hp : 1 < p) :
    |(a+b)/2|^p ≤ (|a|^p+|b|^p)/2 := by
  by_cases hab : a = b
  · subst b
    have he : (a+a)/2 = a := by ring
    rw [he]; linarith
  · exact (abs_midpoint_rpow_strict hp hab).le

lemma lpPower_midpoint_eq_iff {I : Type uI} [Fintype I] (p : ℝ) (hp : 1 < p)
    (u v : I → ℝ) :
    lpPower p (fun i => (u i+v i)/2) = (lpPower p u+lpPower p v)/2 ↔ u = v := by
  constructor
  · intro he
    have hs : ∑ i, ((|u i|^p+|v i|^p)/2 - |(u i+v i)/2|^p) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
      change (lpPower p u + lpPower p v)/2 - lpPower p (fun i => (u i+v i)/2) = 0
      linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sub_nonneg.mpr (abs_midpoint_rpow_le hp))).mp hs
    funext i
    by_contra hh
    have hs := hi i (Finset.mem_univ i)
    linarith [abs_midpoint_rpow_strict hp hh]
  · rintro rfl
    have he (i : I) : (u i+u i)/2 = u i := by ring
    simp only [he]
    ring

lemma lpPower_nonneg {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : 0 ≤ lpPower p x :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma lpPower_neg {I : Type uI} [Fintype I] (p : ℝ) (x : I → ℝ) : lpPower p (-x) = lpPower p x := by
  simp only [lpPower, Pi.neg_apply, abs_neg]

lemma lpPower_smul {I : Type uI} [Fintype I] (p a : ℝ) (x : I → ℝ) :
    lpPower p (a • x) = |a|^p * lpPower p x := by
  simp only [lpPower, Pi.smul_apply, smul_eq_mul, abs_mul,
    Real.mul_rpow (abs_nonneg a) (abs_nonneg _), Finset.mul_sum]

lemma lpPower_midpoint {I : Type uI} [Fintype I] (p : ℝ) (x y : I → ℝ) :
    lpPower p (fun i => (x i+y i)/2) = lpPower p (x+y)/(2:ℝ)^p := by
  simp only [lpPower, abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num),
    Real.div_rpow (abs_nonneg _) (show (0:ℝ)≤2 by norm_num), Finset.sum_div, Pi.add_apply]

lemma antipodes_of_lpPower {I : Type uI} [Fintype I] (p : ℝ) (hp : 1 < p)
    (u v : I → ℝ) (h1 : lpPower p v = lpPower p u)
    (h2 : lpPower p (u-v) = (2:ℝ)^p * lpPower p u) : v = -u := by
  have he : lpPower p (fun i => (u i + (-v) i)/2) = (lpPower p u + lpPower p (-v))/2 := by
    rw [lpPower_midpoint, lpPower_neg, h1, ← sub_eq_add_neg, h2]
    field_simp
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p]
  have hh := (lpPower_midpoint_eq_iff p hp u (-v)).mp he
  simpa using congrArg Neg.neg hh |>.symm

lemma disjoint_rows_columns_card {I : Type uI} {J : Type uJ} {E : Type uE} [Fintype I] [Fintype J] [Fintype E]
    (r : I → E → ℝ) (c : J → E → ℝ)
    (hr : ∀ i i', i ≠ i' → ∀ e, r i e = 0 ∨ r i' e = 0)
    (hc : ∀ j j', j ≠ j' → ∀ e, c j e = 0 ∨ c j' e = 0)
    (hrc : ∀ i j, ∃ e, r i e ≠ 0 ∧ c j e ≠ 0) :
    Fintype.card I * Fintype.card J ≤ Fintype.card E := by
  classical
  choose f hf using hrc
  have hinj : Function.Injective (fun ij : I × J => f ij.1 ij.2) := by
    intro ij ij' he
    change f ij.1 ij.2 = f ij'.1 ij'.2 at he
    apply Prod.ext
    · by_contra hh
      rcases hr _ _ hh (f ij.1 ij.2) with h | h
      · exact (hf _ _).1 h
      · rw [he] at h
        exact (hf _ _).1 h
    · by_contra hh
      rcases hc _ _ hh (f ij.1 ij.2) with h | h
      · exact (hf _ _).2 h
      · rw [he] at h
        exact (hf _ _).2 h
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective _ hinj

end SubpolynomialLp

end

end OAI
