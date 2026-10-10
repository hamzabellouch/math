import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLawConstructions

namespace OAI

section
section
namespace MetricKMedian.MarginalRounding

variable {I : Type*} [Fintype I]

noncomputable def fractional (p : I → ℝ) : Finset I :=
  Finset.univ.filter (fun i => 0 < p i ∧ p i < 1)

@[simp] theorem mem_fractional (p : I → ℝ) (i : I) :
    i ∈ fractional p ↔ 0 < p i ∧ p i < 1 := by simp [fractional]

theorem nonfractional_integral {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i : I} (hi : i ∉ fractional p) : p i=0 ∨ p i=1 := by
  simp only [mem_fractional, not_and_or, not_lt] at hi
  rcases hi with hi | hi
  · exact Or.inl (le_antisymm hi (hp i))
  · exact Or.inr (le_antisymm (hp1 i) hi)

theorem second_fractional {p : I → ℝ} {K : ℕ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = K) {i : I} (hi : i ∈ fractional p) :
    ∃ j ∈ fractional p, j ≠ i := by
  classical
  by_contra h
  push Not at h
  have hother : ∀ j, j ≠ i → j ∉ fractional p := by
    intro j hji hj
    exact hji (h j hj)
  have hi0 := (mem_fractional p i).mp hi
  have hpoint : ∀ j, p j = (if p j=1 then (1:ℝ) else 0)+(if j=i then p i else 0) := by
    intro j
    by_cases hji : j=i
    · subst j
      rw [ite_eq_right (ne_of_lt hi0.2), ite_eq_left rfl, zero_add]
    · rw [ite_eq_right hji, add_zero]
      rcases nonfractional_integral hp hp1 (hother j hji) with hj | hj <;> simp [hj]
  let S := Finset.univ.filter (fun j => p j=1)
  have hid : (∑ j, p j) = (S.card:ℝ)+p i := by
    conv_lhs => arg 2; ext j; rw [hpoint j]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    rw [← Finset.sum_filter]
    simp only [S, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlow : S.card < K := by
    have hh : (S.card:ℝ) < K := by linarith only [hi0.1, hid, hsum]
    exact_mod_cast hh
  have hhigh : K < S.card+1 := by
    have hh : (K:ℝ) < (S.card+1:ℕ) := by push_cast; linarith only [hi0.2, hid, hsum]
    exact_mod_cast hh
  omega

variable [DecidableEq I]

noncomputable def adjust (p : I → ℝ) (i j : I) (t : ℝ) : I → ℝ :=
  fun k => p k+(if k=i then t else 0)-(if k=j then t else 0)

omit [Fintype I] in
@[simp] theorem adjust_left (p : I → ℝ) {i j : I} (hij : i ≠ j) (t : ℝ) :
    adjust p i j t i = p i+t := by simp only [adjust, ite_true, ite_eq_right hij, sub_zero]
omit [Fintype I] in
@[simp] theorem adjust_right (p : I → ℝ) {i j : I} (hij : i ≠ j) (t : ℝ) :
    adjust p i j t j = p j-t := by simp only [adjust, ite_eq_right hij.symm, ite_true, add_zero]
omit [Fintype I] in
theorem adjust_other (p : I → ℝ) {i j k : I} (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) :
    adjust p i j t k = p k := by simp only [adjust, ite_eq_right hki, ite_eq_right hkj, add_zero, sub_zero]

theorem adjust_sum (p : I → ℝ) (i j : I) (t : ℝ) :
    (∑ k, adjust p i j t k) = ∑ k, p k := by
  simp only [adjust, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_sub_cancel_right]

noncomputable def up (p : I → ℝ) (i j : I) : ℝ := min (1-p i) (p j)
noncomputable def down (p : I → ℝ) (i j : I) : ℝ := min (p i) (1-p j)

omit [DecidableEq I] in
theorem up_pos {p : I → ℝ} {i j : I} (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    0 < up p i j := by rw [up, lt_min_iff]; exact ⟨sub_pos.mpr (mem_fractional p i |>.mp hi).2,
      (mem_fractional p j |>.mp hj).1⟩
omit [DecidableEq I] in
theorem down_pos {p : I → ℝ} {i j : I} (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    0 < down p i j := by rw [down, lt_min_iff]; exact ⟨(mem_fractional p i |>.mp hi).1,
      sub_pos.mpr (mem_fractional p j |>.mp hj).2⟩

omit [Fintype I] in
theorem adjust_bounds {p : I → ℝ} (hp : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {i j : I} (hij : i ≠ j) {t : ℝ} (ht0 : -down p i j ≤ t) (ht1 : t ≤ up p i j) :
    (∀ k, 0 ≤ adjust p i j t k) ∧ (∀ k, adjust p i j t k ≤ 1) := by
  have htlow1 := min_le_left (p i) (1-p j)
  have htlow2 := min_le_right (p i) (1-p j)
  have hthigh1 := min_le_left (1-p i) (p j)
  have hthigh2 := min_le_right (1-p i) (p j)
  change -min (p i) (1-p j) ≤ t at ht0
  change t ≤ min (1-p i) (p j) at ht1
  constructor <;> intro k <;> by_cases hki : k=i
  · subst k; rw [adjust_left p hij]; linarith only [ht0, htlow1]
  · by_cases hkj : k=j
    · subst k; rw [adjust_right p hij]; linarith only [ht1, hthigh2]
    · rw [adjust_other p hki hkj]; exact hp k
  · subst k; rw [adjust_left p hij]; linarith only [ht1, hthigh1]
  · by_cases hkj : k=j
    · subst k; rw [adjust_right p hij]; linarith only [ht0, htlow2]
    · rw [adjust_other p hki hkj]; exact hp1 k

theorem fractional_adjust_subset {p : I → ℝ} {i j : I}
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) (t : ℝ) :
    fractional (adjust p i j t) ⊆ fractional p := by
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using hi
  by_cases hkj : k=j
  · simpa only [hkj] using hj
  simpa only [mem_fractional, adjust_other p hki hkj] using hk

theorem up_smaller {p : I → ℝ} {i j : I} (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (adjust p i j (up p i j))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_adjust_subset hi hj _, ?_⟩
  intro heq
  rcases le_total (1-p i) (p j) with h | h
  · have hv : adjust p i j (up p i j) i = 1 := by rw [adjust_left p hij, up, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (adjust p i j (up p i j)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : adjust p i j (up p i j) j = 0 := by rw [adjust_right p hij, up, min_eq_right h]; ring
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (adjust p i j (up p i j)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem down_smaller {p : I → ℝ} {i j : I} (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (adjust p i j (-down p i j))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_adjust_subset hi hj _, ?_⟩
  intro heq
  rcases le_total (p i) (1-p j) with h | h
  · have hv : adjust p i j (-down p i j) i = 0 := by rw [adjust_left p hij, down, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (adjust p i j (-down p i j)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : adjust p i j (-down p i j) j = 1 := by rw [adjust_right p hij, down, min_eq_right h]; ring
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (adjust p i j (-down p i j)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem exists_law (p : I → ℝ) (K : ℕ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = K) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → S.card = K) ∧
      (∀ i, μ.prob (fun S => i ∈ S) = p i) := by
  classical
  suffices h : ∀ n : ℕ, ∀ q : I → ℝ, (fractional q).card = n →
      (∀ i, 0 ≤ q i) → (∀ i, q i ≤ 1) → (∑ i, q i = K) →
      ∃ μ : FiniteLaw (Finset I),
        (∀ S, 0 < μ.weight S → S.card = K) ∧
        (∀ i, μ.prob (fun S => i ∈ S) = q i) from
    h _ p rfl hp hp1 hsum
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hn hq0 hq1 hsum
    by_cases hempty : fractional q = ∅
    · let S := Finset.univ.filter (fun i => q i=1)
      have hpoint : ∀ i, (if i ∈ S then (1:ℝ) else 0)=q i := by
        intro i
        have hnot : i ∉ fractional q := by rw [hempty]; exact Finset.notMem_empty i
        rcases nonfractional_integral hq0 hq1 hnot with hz | hone
        · simp [S, hz]
        · simp [S, hone]
      have hcard : S.card=K := by
        have hc : (S.card:ℝ) = ∑ i, q i := by
          calc
            (S.card:ℝ) = ∑ i, if i ∈ S then (1:ℝ) else 0 := by simp
            _ = ∑ i, q i := Finset.sum_congr rfl (fun i _ => hpoint i)
        exact_mod_cast hc.trans hsum
      refine ⟨FiniteLaw.dirac S, ?_, ?_⟩
      · intro T hT
        by_cases hTS : T=S
        · simpa [hTS] using hcard
        · simp only [FiniteLaw.dirac, ite_eq_right hTS] at hT
          exact False.elim (lt_irrefl _ hT)
      · intro i
        rw [FiniteLaw.prob, FiniteLaw.expect_dirac]
        exact hpoint i
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨j, hj, hji⟩ := second_fractional hq0 hq1 hsum hi
      have hu := up_pos hi hj
      have hd := down_pos hi hj
      have hsumpos : 0 < up q i j+down q i j := add_pos hu hd
      have hqplus := adjust_bounds hq0 hq1 hji.symm (by linarith) (le_refl (up q i j))
      have hqminus := adjust_bounds hq0 hq1 hji.symm (le_refl (-down q i j)) (by linarith)
      obtain ⟨μ, hμcard, hμmarg⟩ := ih _ (hn ▸ up_smaller hji.symm hi hj)
        (adjust q i j (up q i j)) rfl hqplus.1 hqplus.2
        ((adjust_sum _ _ _ _).trans hsum)
      obtain ⟨ν, hνcard, hνmarg⟩ := ih _ (hn ▸ down_smaller hji.symm hi hj)
        (adjust q i j (-down q i j)) rfl hqminus.1 hqminus.2
        ((adjust_sum _ _ _ _).trans hsum)
      let θ := down q i j/(up q i j+down q i j)
      have hθ0 : 0 ≤ θ := le_of_lt (div_pos hd hsumpos)
      have hθ1 : θ ≤ 1 := (div_le_one hsumpos).mpr (by linarith)
      refine ⟨FiniteLaw.mix θ hθ0 hθ1 μ ν, ?_, ?_⟩
      · intro S hS
        by_cases hμ : 0 < μ.weight S
        · exact hμcard S hμ
        · have hz : μ.weight S=0 := le_antisymm (le_of_not_gt hμ) (μ.nonneg S)
          have hν : 0 < ν.weight S := by
            by_contra hnν
            have hzν : ν.weight S=0 := le_antisymm (le_of_not_gt hnν) (ν.nonneg S)
            simp only [FiniteLaw.mix, hz, hzν, mul_zero, add_zero] at hS
            exact lt_irrefl _ hS
          exact hνcard S hν
      · intro k
        unfold FiniteLaw.prob
        rw [FiniteLaw.expect_mix]
        change θ*μ.prob (fun S => k ∈ S)+(1-θ)*ν.prob (fun S => k ∈ S)=q k
        rw [hμmarg, hνmarg]
        dsimp only [θ, adjust]
        split_ifs <;> field_simp <;> ring

end MetricKMedian.MarginalRounding
end
end

end OAI
