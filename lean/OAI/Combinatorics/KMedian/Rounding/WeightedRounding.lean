import Mathlib
import OAI.Combinatorics.KMedian.Geometry.GraphLaw
import OAI.Combinatorics.KMedian.Probability.BernoulliBatches
import OAI.Combinatorics.KMedian.Probability.FiniteKernels

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

noncomputable def sign (i j : I) (r : ℝ) (k : I) : ℝ :=
  (if k=i then 1 else 0)-(if k=j then r else 0)
noncomputable def move (p : I → ℝ) (i j : I) (r t : ℝ) : I → ℝ :=
  fun k => p k+t*sign i j r k
noncomputable def up (p : I → ℝ) (i j : I) (r : ℝ) := min (1-p i) (p j/r)
noncomputable def down (p : I → ℝ) (i j : I) (r : ℝ) := min (p i) ((1-p j)/r)

omit [Fintype I] in
theorem sign_distinct {i j k l : I} {r : ℝ} (hr : 0 ≤ r) (hkl : k ≠ l) :
    sign i j r k*sign i j r l ≤ 0 := by
  unfold sign
  split_ifs <;> simp_all

omit [Fintype I] in
theorem move_left (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t i=p i+t := by simp only [move, sign, ite_true, ite_eq_right hij, sub_zero, mul_one]
omit [Fintype I] in
theorem move_right (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t j=p j-r*t := by simp only [move, sign, ite_eq_right hij.symm, ite_true, zero_sub]; ring
omit [Fintype I] in
theorem move_other (p : I → ℝ) {i j k : I} (hki : k ≠ i) (hkj : k ≠ j) (r t : ℝ) :
    move p i j r t k=p k := by simp only [move, sign, ite_eq_right hki, ite_eq_right hkj, sub_self, mul_zero, add_zero]

omit [DecidableEq I] in
theorem up_pos {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < up p i j r := by
  exact lt_min (sub_pos.mpr (mem_fractional p i |>.mp hi).2)
    (div_pos (mem_fractional p j |>.mp hj).1 hr)
omit [DecidableEq I] in
theorem down_pos {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < down p i j r := by
  exact lt_min (mem_fractional p i |>.mp hi).1
    (div_pos (sub_pos.mpr (mem_fractional p j |>.mp hj).2) hr)

omit [Fintype I] in
theorem move_bounds {p : I → ℝ} (hp : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {i j : I} (hij : i ≠ j) {r t : ℝ} (hr : 0 < r)
    (ht0 : -down p i j r ≤ t) (ht1 : t ≤ up p i j r) :
    (∀ k, 0 ≤ move p i j r t k) ∧ (∀ k, move p i j r t k ≤ 1) := by
  have hl1 := min_le_left (p i) ((1-p j)/r)
  have hl2 := (le_div_iff₀ hr).mp (min_le_right (p i) ((1-p j)/r))
  have hu1 := min_le_left (1-p i) (p j/r)
  have hu2 := (le_div_iff₀ hr).mp (min_le_right (1-p i) (p j/r))
  have htl := mul_le_mul_of_nonneg_left ht0 hr.le
  have htu := mul_le_mul_of_nonneg_left ht1 hr.le
  change -min (p i) ((1-p j)/r) ≤ t at ht0
  change t ≤ min (1-p i) (p j/r) at ht1
  change r * -min (p i) ((1-p j)/r) ≤ r*t at htl
  change r*t ≤ r*min (1-p i) (p j/r) at htu
  constructor <;> intro k <;> by_cases hki : k=i
  · subst k; rw [move_left p hij]; linarith only [ht0, hl1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htu, hu2]
    · rw [move_other p hki hkj]; exact hp k
  · subst k; rw [move_left p hij]; linarith only [ht1, hu1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htl, hl2]
    · rw [move_other p hki hkj]; exact hp1 k

theorem fractional_subset {p : I → ℝ} {i j : I}
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) (r t : ℝ) :
    fractional (move p i j r t) ⊆ fractional p := by
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using hi
  by_cases hkj : k=j
  · simpa only [hkj] using hj
  simpa only [mem_fractional, move_other p hki hkj] using hk

theorem up_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (up p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (1-p i) (p j/r) with h | h
  · have hv : move p i j r (up p i j r) i=1 := by rw [move_left p hij, up, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (up p i j r) j=0 := by
      rw [move_right p hij, up, min_eq_right h, mul_div_cancel₀ _ (ne_of_gt hr), sub_self]
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem down_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (-down p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (p i) ((1-p j)/r) with h | h
  · have hv : move p i j r (-down p i j r) i=0 := by rw [move_left p hij, down, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (-down p i j r) j=1 := by
      rw [move_right p hij, down, min_eq_right h, mul_neg, mul_div_cancel₀ _ (ne_of_gt hr)]; ring
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem weighted_sum (β p : I → ℝ) {i j : I} (hj : β j ≠ 0) (t : ℝ) :
    (∑ k, β k*move p i j (β i/β j) t k)=∑ k, β k*p k := by
  simp only [move, sign, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

omit [Fintype I] in

theorem endpoint_mean (p : I → ℝ) (i j k : I) (r : ℝ) {u d : ℝ}
    (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*move p i j r u k+(1-d/(u+d))*move p i j r (-d) k=p k := by
  unfold move
  field_simp
  ring

omit [Fintype I] in
theorem endpoint_pair (p : I → ℝ) (i j : I) {k l : I} (hkl : k ≠ l) {r u d : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hd : 0 < d) :
    d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) ≤ p k*p l := by
  have hpos : 0 < u+d := add_pos hu hd
  have hid : d/(u+d)*(move p i j r u k*move p i j r u l)+
      (1-d/(u+d))*(move p i j r (-d) k*move p i j r (-d) l) =
      p k*p l+u*d*(sign i j r k*sign i j r l) := by
    unfold move
    field_simp
    ring
  rw [hid]
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le hd.le)
    (sign_distinct hr hkl))

noncomputable def indicator (S : Finset I) (i : I) : ℝ := if i ∈ S then 1 else 0

theorem last_fraction (p β : I → ℝ) {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hβ0 : ∀ i, 0 ≤ β i) (hβM : ∀ i, β i ≤ M) (hM : 0 ≤ M)
    (hsmall : (fractional p).card ≤ 1) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → |(∑ i ∈ S, β i)-(∑ i, β i*p i)| ≤ M) ∧
      (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j)=p i*p j) := by
  classical
  let ν := FiniteLaw.bernoulli p hp0 hp1
  let select : (I → Bool) → Finset I := fun ω => Finset.univ.filter (fun i => ω i=true)
  have hmarg : ∀ i, ν.prob (fun ω => ω i=true)=p i := FiniteLaw.bernoulli_marginal p hp0 hp1
  have hfixed : ∀ ω, 0 < ν.weight ω → ∀ i, i ∉ fractional p →
      (if ω i=true then (1:ℝ) else 0)=p i := by
    intro ω hω i hi
    rcases nonfractional_integral hp0 hp1 hi with hi0 | hi1
    · have hn := ν.not_property_of_prob_zero (fun ω => ω i=true) ((hmarg i).trans hi0) hω
      simp only [ite_eq_right hn, hi0]
    · have hy := ν.property_of_prob_one (fun ω => ω i=true) ((hmarg i).trans hi1) hω
      simp only [ite_eq_left hy, hi1]
  refine ⟨ν.map select, ?_, ?_, ?_⟩
  · apply ν.property_map select
    intro ω hω
    have hid : (∑ i ∈ select ω, β i)-(∑ i, β i*p i) =
        ∑ i, β i*((if ω i=true then (1:ℝ) else 0)-p i) := by
      simp only [select, Finset.sum_filter, mul_sub, mul_ite, mul_one, mul_zero,
        Finset.sum_sub_distrib]
    rw [hid]
    by_cases he : fractional p=∅
    · have hz : ∀ i, β i*((if ω i=true then (1:ℝ) else 0)-p i)=0 := by
        intro i
        rw [hfixed ω hω i (by rw [he]; exact Finset.notMem_empty i), sub_self, mul_zero]
      simpa only [hz, Finset.sum_const_zero, abs_zero] using hM
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hother : ∀ k, k ≠ i → k ∉ fractional p := by
        intro k hki hk
        exact hki (Finset.card_le_one.mp hsmall k hk i hi)
      have hsum : (∑ k, β k*((if ω k=true then (1:ℝ) else 0)-p k)) =
          β i*((if ω i=true then (1:ℝ) else 0)-p i) := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          rw [hfixed ω hω k (hother k hki), sub_self, mul_zero]
        · intro hn; exact False.elim (hn (Finset.mem_univ i))
      rw [hsum, abs_mul, abs_of_nonneg (hβ0 i)]
      have hnoise : |(if ω i=true then (1:ℝ) else 0)-p i| ≤ 1 := by
        apply abs_le.mpr
        split_ifs <;> constructor <;> linarith only [hp0 i, hp1 i]
      exact (mul_le_mul_of_nonneg_left hnoise (hβ0 i)).trans (by simpa only [mul_one] using hβM i)
  · intro i
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_map]
    simpa only [FiniteLaw.prob, select, Finset.mem_filter, Finset.mem_univ, true_and] using hmarg i
  · intro i j hij
    rw [FiniteLaw.expect_map]
    have hpoint : ∀ ω, indicator (select ω) i*indicator (select ω) j =
        if ω i=true ∧ ω j=true then (1:ℝ) else 0 := by
      intro ω
      simp only [indicator, select, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    simp_rw [hpoint]
    exact FiniteLaw.bernoulli_pair p hp0 hp1 hij

theorem exists_law (p β : I → ℝ) {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hβ : ∀ i, 0 < β i) (hβM : ∀ i, β i ≤ M) (hM : 0 ≤ M) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → |(∑ i ∈ S, β i)-(∑ i, β i*p i)| ≤ M) ∧
      (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j) := by
  classical
  suffices h : ∀ n : ℕ, ∀ p : I → ℝ, (fractional p).card=n →
      (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
      ∃ μ : FiniteLaw (Finset I),
        (∀ S, 0 < μ.weight S → |(∑ i ∈ S, β i)-(∑ i, β i*p i)| ≤ M) ∧
        (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
        (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j) by
    exact h _ p rfl hp0 hp1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp0 hp1
    by_cases hsmall : (fractional p).card ≤ 1
    · obtain ⟨μ, hsum, hmarg, hpair⟩ := last_fraction p β hp0 hp1 (fun i => (hβ i).le) hβM hM hsmall
      exact ⟨μ, hsum, hmarg, fun i j hij => (hpair i j hij).le⟩
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_not_ge hsmall)
    let r : ℝ := β i/β j
    have hr : 0 < r := div_pos (hβ i) (hβ j)
    let u := up p i j r
    let d := down p i j r
    have hu : 0 < u := up_pos hr hi hj
    have hd : 0 < d := down_pos hr hi hj
    have bud := move_bounds hp0 hp1 hij hr (show -d ≤ u by linarith) (le_refl u)
    have bdd := move_bounds hp0 hp1 hij hr (le_refl (-d)) (show -d ≤ u by linarith)
    obtain ⟨μ, hsμ, hmμ, hpμ⟩ := ih _ (hn ▸ up_smaller hr hij hi hj) (move p i j r u) rfl bud.1 bud.2
    obtain ⟨ν, hsν, hmν, hpν⟩ := ih _ (hn ▸ down_smaller hr hij hi hj) (move p i j r (-d)) rfl bdd.1 bdd.2
    let θ : ℝ := d/(u+d)
    have hθ0 : 0 ≤ θ := (div_pos hd (add_pos hu hd)).le
    have hθ1 : θ ≤ 1 := (div_le_one (add_pos hu hd)).mpr (by linarith)
    have hwμ : (∑ k, β k*move p i j r u k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) u
    have hwν : (∑ k, β k*move p i j r (-d) k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) (-d)
    refine ⟨FiniteLaw.mix θ hθ0 hθ1 μ ν, ?_, ?_, ?_⟩
    · apply FiniteLaw.property_mix μ ν hθ0 hθ1
      · intro S hS
        simpa only [hwμ] using hsμ S hS
      · intro S hS
        simpa only [hwν] using hsν S hS
    · intro k
      simp only [FiniteLaw.prob, FiniteLaw.expect_mix]
      change θ*μ.prob (fun S => k ∈ S)+(1-θ)*ν.prob (fun S => k ∈ S)=p k
      rw [hmμ, hmν]
      exact endpoint_mean p i j k r hu hd
    · intro k l hkl
      rw [FiniteLaw.expect_mix]
      calc
        _ ≤ θ*(move p i j r u k*move p i j r u l)+
            (1-θ)*(move p i j r (-d) k*move p i j r (-d) l) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpμ k l hkl) hθ0)
            (mul_le_mul_of_nonneg_left (hpν k l hkl) (sub_nonneg.mpr hθ1))
        _ ≤ p k*p l := endpoint_pair p i j hkl hr.le hu hd

end MetricKMedian.WeightedRounding
end
end

end OAI
