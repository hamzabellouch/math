import OAI.Combinatorics.CliqueFree.Model

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

/-- A finite real-valued probability vector. -/
def IsProb (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Weighted row entropy, with the `0 log 0 = 0` convention. -/
def entropy (w p : I → ℝ) : ℝ := ∑ i, p i * Real.log (w i / p i)

/-- Relative entropy, used only when `q` is positive on the positive support of `p`. -/
def divergence (p q : I → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Total variation distance of two finite probability vectors. -/
def tv (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

lemma relTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) : 0 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, hq]
  have hq' := hs hp
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp)
  have hl : Real.log (q / p) = -Real.log (p / q) := by
    rw [Real.log_div hq'.ne' hp.ne', Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have hc : p * (q / p - 1) = q - p := by field_simp
  rw [hc] at hm
  linarith

lemma sqrt_sub_sq_le_relTerm {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, Real.sq_sqrt hq]
  have hq' := hs hp
  have hsp := Real.sqrt_pos.2 hp
  have hsq := Real.sqrt_pos.2 hq'
  have h := Real.log_le_sub_one_of_pos (div_pos hsq hsp)
  have hl : Real.log (Real.sqrt q / Real.sqrt p) = -(Real.log (p / q)) / 2 := by
    rw [Real.log_div hsq.ne' hsp.ne', Real.log_sqrt hq, Real.log_sqrt hp.le,
      Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * p by positivity)
  have hc : p * (Real.sqrt q / Real.sqrt p) = Real.sqrt p * Real.sqrt q := by
    calc
      _ = (Real.sqrt p) ^ 2 * (Real.sqrt q / Real.sqrt p) := by rw [Real.sq_sqrt hp.le]
      _ = Real.sqrt p * Real.sqrt q := by field_simp
  have hp2 := Real.sq_sqrt hp.le
  have hq2 := Real.sq_sqrt hq
  nlinarith

lemma divergence_nonneg {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) : 0 ≤ divergence p q := by
  have h := sum_nonneg (s := univ) fun i _ ↦ relTerm_nonneg (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

lemma hellinger_le_divergence {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) ≤ divergence p q := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    sqrt_sub_sq_le_relTerm (hp.1 i) (hq.1 i) (hs i)
  simpa [divergence, sum_add_distrib, sum_sub_distrib, hp.2, hq.2] using h

lemma tv_nonneg (p q : I → ℝ) : 0 ≤ tv p q := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)

lemma tv_sq_le_hellinger {p q : I → ℝ} (hp : IsProb p) (hq : IsProb q) :
    tv p q ^ 2 ≤ ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
  let f := fun i ↦ |Real.sqrt (p i) - Real.sqrt (q i)|
  let g := fun i ↦ Real.sqrt (p i) + Real.sqrt (q i)
  have hfactor (i : I) : |p i - q i| = f i * g i := by
    have he : p i - q i =
        (Real.sqrt (p i) - Real.sqrt (q i)) *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
      nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i))]
  have hsum : (∑ i, f i ^ 2) + (∑ i, g i ^ 2) = 4 := by
    rw [← sum_add_distrib]
    calc
      _ = (∑ i, (2 * p i + 2 * q i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [f, g]
        rw [sq_abs]
        nlinarith [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
      _ = 4 := by norm_num [sum_add_distrib, ← mul_sum, hp.2, hq.2]
  have hf0 : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hg4 : ∑ i, g i ^ 2 ≤ 4 := by linarith
  have hc := sum_mul_sq_le_sq_mul_sq univ f g
  have hle := mul_le_mul_of_nonneg_left hg4 hf0
  have he : (∑ i, f i ^ 2) = ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
    simp [f]
  rw [tv, show (∑ i, |p i - q i|) = ∑ i, f i * g i from sum_congr rfl (fun i _ ↦ hfactor i)]
  rw [← he]
  nlinarith

lemma entropy_eq_sum {w p : I → ℝ} (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 ≤ p i) :
    entropy w p = ∑ i, (p i * Real.log (w i) - p i * Real.log (p i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div (hw i).ne' hi.ne', mul_sub]

lemma divergence_eq_sum {p q : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    divergence p q = ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div hi.ne' (hs i hi).ne', mul_sub]

lemma entropy_ge_neg_log_of_density {w p : I → ℝ} (_hw : ∀ i, 0 < w i)
    (hp : IsProb p) {b : ℝ} (hb : 0 < b) (hden : ∀ i, p i ≤ b * w i) :
    -Real.log b ≤ entropy w p := by
  have hi (i : I) : p i * (-Real.log b) ≤ p i * Real.log (w i / p i) := by
    rcases (hp.1 i).eq_or_lt with hi | hi
    · simp [← hi]
    apply mul_le_mul_of_nonneg_left _ hi.le
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.2 hb)
    apply (le_div_iff₀ hi).2
    calc
      b⁻¹ * p i = p i / b := by ring
      _ ≤ w i := (div_le_iff₀ hb).2 (by simpa [mul_comm] using hden i)
  have h := sum_le_sum (s := univ) fun i _ ↦ hi i
  simpa [← sum_mul, hp.2, entropy] using h

lemma tv_comm (p q : I → ℝ) : tv p q = tv q p := by
  simp only [tv, abs_sub_comm]

lemma tv_triangle (p q r : I → ℝ) : tv p r ≤ tv p q + tv q r := by
  have h := sum_le_sum (s := univ) fun i _ ↦ abs_sub_le (p i) (q i) (r i)
  simpa only [sum_add_distrib, tv, ← add_div] using div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

lemma weighted_sq_le {a f : I → ℝ} (ha : IsProb a) :
    (∑ i, a i * f i) ^ 2 ≤ ∑ i, a i * (f i) ^ 2 := by
  let m := ∑ i, a i * f i
  have h := sum_nonneg (s := univ) fun i _ ↦
    mul_nonneg (ha.1 i) (sq_nonneg (f i - m))
  have he : (∑ i, a i * (f i - m) ^ 2) = (∑ i, a i * (f i) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ i, (a i * (f i) ^ 2 - 2 * (a i * f i) * m + a i * m ^ 2) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ha.2]
        dsimp [m]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

omit [Fintype I] in
lemma mix_support {a : J → ℝ} {p : J → I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ j i, 0 ≤ p j i) {j : J} (hj : 0 < a j) {i : I} (hi : 0 < p j i) :
    0 < ∑ k, a k * p k i := by
  classical
  exact (mul_pos hj hi).trans_le (single_le_sum
    (fun k _ ↦ mul_nonneg (ha k) (hp k i)) (mem_univ j))

/-- The finite entropy-mixture identity for the averaged increment. -/
lemma entropy_mix_gap {w : I → ℝ} (hw : ∀ i, 0 < w i)
    {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a) (hp : ∀ j, IsProb (p j)) :
    entropy w (fun i ↦ ∑ j, a j * p j i) - ∑ j, a j * entropy w (p j) =
      ∑ j, a j * divergence (p j) (fun i ↦ ∑ k, a k * p k i) := by
  let b := fun i ↦ ∑ j, a j * p j i
  have hb := mix_isProb ha hp
  have hd (j : J) : a j * divergence (p j) b =
      a j * (∑ i, (p j i * Real.log (p j i) - p j i * Real.log (b i))) := by
    rcases (ha.1 j).eq_or_lt with hj | hj
    · simp [← hj]
    · rw [divergence_eq_sum (hp j).1
        (fun i hi ↦ mix_support ha.1 (fun k ↦ (hp k).1) hj hi)]
  change entropy w b - ∑ j, a j * entropy w (p j) = ∑ j, a j * divergence (p j) b
  rw [entropy_eq_sum hw hb.1]
  simp_rw [entropy_eq_sum hw (hp _).1, hd, mul_sum, mul_sub, sum_sub_distrib]
  have he (f : I → ℝ) : (∑ i, b i * f i) = ∑ j, ∑ i, a j * (p j i * f i) := by
    dsimp [b]
    simp_rw [sum_mul, mul_assoc]
    rw [sum_comm]
  rw [he, he]
  ring

lemma average_tv_sq_le_average_divergence {a : J → ℝ} (ha : IsProb a)
    {p q : J → I → ℝ} (hp : ∀ j, IsProb (p j)) (hq : ∀ j, IsProb (q j))
    (hs : ∀ j, 0 < a j → ∀ i, 0 < p j i → 0 < q j i) :
    (∑ j, a j * tv (p j) (q j)) ^ 2 ≤ ∑ j, a j * divergence (p j) (q j) := by
  apply (weighted_sq_le ha).trans
  apply sum_le_sum
  intro j _
  rcases (ha.1 j).eq_or_lt with hj | hj
  · simp [← hj]
  apply mul_le_mul_of_nonneg_left _ hj.le
  exact (tv_sq_le_hellinger (hp j) (hq j)).trans
    (hellinger_le_divergence (hp j) (hq j) (hs j hj))

omit [Fintype I] in
lemma mul_log_div {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    p * Real.log (w / p) = p * Real.log w - p * Real.log p := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  · rw [Real.log_div hw.ne' hp.ne', mul_sub]

omit [Fintype I] in
lemma partial_entropy_le (s : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hp : ∀ i ∈ s, 0 ≤ p i)
    {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ s, w i ≤ m) :
    (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
      (∑ i ∈ s, p i) * Real.log (m / (∑ i ∈ s, p i)) := by
  let t := ∑ i ∈ s, p i
  have ht : 0 ≤ t := sum_nonneg hp
  rcases ht.eq_or_lt with ht | ht
  · have hz : ∀ i ∈ s, p i = 0 := (sum_eq_zero_iff_of_nonneg hp).1 ht.symm
    simp only [show (∑ i ∈ s, p i) = 0 from ht.symm, zero_mul]
    apply le_of_eq
    exact sum_eq_zero (fun i hi ↦ by rw [hz i hi, zero_mul])
  have hi (i : I) (his : i ∈ s) :
      p i * Real.log (w i / p i) ≤ p i * Real.log (m / t) - p i + t * w i / m := by
    rcases (hp i his).eq_or_lt with hpi | hpi
    · simp only [← hpi, zero_mul, sub_self, zero_add]
      exact (div_pos (mul_pos ht (hw i his)) hm).le
    have hq : 0 < t * w i / m := div_pos (mul_pos ht (hw i his)) hm
    have hr := relTerm_nonneg hpi.le hq.le (fun _ ↦ hq)
    have hl : Real.log (p i / (t * w i / m)) =
        Real.log (m / t) - Real.log (w i / p i) := by
      rw [Real.log_div hpi.ne' hq.ne',
        Real.log_div (mul_pos ht (hw i his)).ne' hm.ne',
        Real.log_mul ht.ne' (hw i his).ne',
        Real.log_div hm.ne' ht.ne', Real.log_div (hw i his).ne' hpi.ne']
      ring
    rw [hl] at hr
    nlinarith
  have h := sum_le_sum hi
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_div, ← mul_sum] at h
  have hq : t * (∑ i ∈ s, w i) / m ≤ t := by
    apply (div_le_iff₀ hm).2
    exact mul_le_mul_of_nonneg_left hwm ht.le
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤ t * Real.log (m / t)
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
    t * Real.log (m / t) - t + t * (∑ i ∈ s, w i) / m at h
  linarith

lemma prob_sum_on {p : I → ℝ} (hp : IsProb p) (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : ∑ i ∈ D, p i = 1 := by
  rw [← hp.2]
  exact sum_subset (subset_univ _) (fun i _ hi ↦ hs i hi)

lemma entropy_sum_on {w p : I → ℝ} (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : entropy w p = ∑ i ∈ D, p i * Real.log (w i / p i) := by
  symm
  apply sum_subset (subset_univ _)
  intro i _ hi
  rw [hs i hi, zero_mul]

lemma entropy_supported_le_log (D : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p)
    (hs : ∀ i, i ∉ D → p i = 0) {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ D, w i ≤ m) :
    entropy w p ≤ Real.log m := by
  have h := partial_entropy_le D hw (fun i _ ↦ hp.1 i) hm hwm
  simpa only [prob_sum_on hp D hs, div_one, one_mul, ← entropy_sum_on D hs] using h

lemma entropy_supported_concentration (D s : Finset I) (hsD : s ⊆ D) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p) (hs : ∀ i, i ∉ D → p i = 0)
    {m M : ℝ} (hm : 1 ≤ m) (hM : 0 < M)
    (hwsmall : ∑ i ∈ s, w i ≤ m) (hwall : ∑ i ∈ D, w i ≤ M) :
    entropy w p ≤ Real.log 2 + Real.log m + (1 - ∑ i ∈ s, p i) * Real.log M := by
  classical
  let t := ∑ i ∈ s, p i
  let d := ∑ i ∈ D \ s, p i
  have ht : 0 ≤ t := sum_nonneg fun i _ ↦ hp.1 i
  have hd : 0 ≤ d := sum_nonneg fun i _ ↦ hp.1 i
  have htd : d + t = 1 := by
    dsimp [t, d]
    rw [sum_sdiff hsD, prob_sum_on hp D hs]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hwc : (∑ i ∈ D \ s, w i) ≤ M := by
    apply le_trans _ hwall
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i hi _ ↦ (hw i hi).le)
  have ha := partial_entropy_le s (fun i hi ↦ hw i (hsD hi)) (fun i _ ↦ hp.1 i) hm0 hwsmall
  have hc := partial_entropy_le (D \ s) (fun i hi ↦ hw i (mem_sdiff.1 hi).1)
    (fun i _ ↦ hp.1 i) hM hwc
  have he : entropy w p ≤ d * Real.log (M / d) + t * Real.log (m / t) := by
    rw [entropy_sum_on D hs, ← sum_sdiff hsD]
    exact add_le_add hc ha
  rw [mul_log_div hd hM, mul_log_div ht hm0] at he
  have hbin : -t * Real.log t - d * Real.log d ≤ Real.log 2 := by
    have hb := Real.binEntropy_le_log_two (p := t)
    have hd' : d = 1 - t := by linarith
    rw [hd']
    simpa [Real.binEntropy, Real.log_inv] using hb
  have hl := Real.log_nonneg hm
  have ht1 : t ≤ 1 := by linarith
  have hmterm : t * Real.log m ≤ Real.log m := by nlinarith
  change entropy w p ≤ Real.log 2 + Real.log m + (1 - t) * Real.log M
  have hd' : 1 - t = d := by linarith
  rw [hd']
  linarith

lemma entropy_tail_term {p w x a : ℝ} (hp : 0 ≤ p) (hw : 0 < w)
    (hx : 0 < x) (hd : p ≤ x * w) :
    (a + Real.log x) * (if p < w * Real.exp (-a) then p else 0) ≤
      p * (Real.log (w / p) + Real.log x) := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  have hlog := Real.log_le_log hp hd
  rw [Real.log_mul hx.ne' hw.ne'] at hlog
  have hlower : 0 ≤ Real.log (w / p) + Real.log x := by
    rw [Real.log_div hw.ne' hp.ne']
    linarith
  split_ifs with hsmall
  · have h := Real.log_lt_log hp hsmall
    rw [Real.log_mul hw.ne' (Real.exp_ne_zero _), Real.log_exp] at h
    have ha : a ≤ Real.log (w / p) := by
      rw [Real.log_div hw.ne' hp.ne']
      linarith
    nlinarith
  · simpa using mul_nonneg hp.le hlower

lemma entropy_tail {p w : I → ℝ} (hp : IsProb p) (hw : ∀ i, 0 < w i)
    {x a : ℝ} (hx : 0 < x) (hd : ∀ i, p i ≤ x * w i) :
    (a + Real.log x) * (∑ i, if p i < w i * Real.exp (-a) then p i else 0) ≤
      entropy w p + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    entropy_tail_term (a := a) (hp.1 i) (hw i) hx (hd i)
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hp.2, one_mul,
    entropy] using h

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI
