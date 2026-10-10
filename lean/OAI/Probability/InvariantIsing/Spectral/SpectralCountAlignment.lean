import OAI.Probability.InvariantIsing.Spectral.SpectralGroupMass

namespace OAI

/-! Align two finite spectral labelings so each common eigenspace retains
as many axes as possible. A maximizing permutation has no unmatched pair
that can be improved by a transposition. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma exists_spectral_label_alignment {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) :
    ∃ p : Equiv.Perm ι, ∀ v : A,
      (∀ i, a i = v → b (p i) = v) ∨ (∀ i, b (p i) = v → a i = v) := by
  classical
  let matchSet := fun p : Equiv.Perm ι => Finset.univ.filter fun i => a i = b (p i)
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : Equiv.Perm ι => (matchSet p).card) Finset.univ_nonempty
  refine ⟨p, fun v => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨⟨i, hi, hbi⟩, j, hj, haj⟩ := h
  have hij : i ≠ j := by
    intro he
    subst j
    exact hbi hj
  let q : Equiv.Perm ι := (Equiv.swap i j).trans p
  have hqi : q i = p j := by simp [q]
  have hqk k (hki : k ≠ i) (hkj : k ≠ j) : q k = p k := by
    simp only [q, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hsub : matchSet p ⊆ matchSet q := by
    intro k hk
    have hk' : a k = b (p k) := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro he
      subst k
      exact hbi (hk'.symm.trans hi)
    have hkj : k ≠ j := by
      intro he
      subst k
      exact haj (hk'.trans hj)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ k, by rw [hqk k hki hkj]; exact hk'⟩
  have hin : i ∈ matchSet q := Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, by rw [hqi]; exact hi.trans hj.symm⟩
  have hout : i ∉ matchSet p := by
    intro hi'
    exact hbi ((Finset.mem_filter.mp hi').2.symm.trans hi)
  have hstrict : (matchSet p).card < (matchSet q).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, by intro he; rw [← he] at hin; exact hout hin⟩)
  exact (not_lt_of_ge (hp q (Finset.mem_univ q))) hstrict

lemma spectral_alignment_common_count {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) (p : Equiv.Perm ι) (v : A)
    (hp : (∀ i, a i = v → b (p i) = v) ∨ (∀ i, b (p i) = v → a i = v)) :
    ((Finset.univ.filter fun i => a i = v ∧ b (p i) = v).card) =
      min ((Finset.univ.filter fun i => a i = v).card)
        ((Finset.univ.filter fun i => b (p i) = v).card) := by
  let left := Finset.univ.filter fun i => a i = v
  let right := Finset.univ.filter fun i => b (p i) = v
  let both := Finset.univ.filter fun i => a i = v ∧ b (p i) = v
  change both.card = min left.card right.card
  rcases hp with hp | hp
  · have hsub : left ⊆ right := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp i (Finset.mem_filter.mp hi).2⟩
    have he : both = left := by
      ext i
      simp only [both, left, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => hi.1, fun hi => ⟨hi, hp i hi⟩⟩
    rw [he, min_eq_left (Finset.card_le_card hsub)]
  · have hsub : right ⊆ left := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp i (Finset.mem_filter.mp hi).2⟩
    have he : both = right := by
      ext i
      simp only [both, right, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => hi.2, fun hi => ⟨hp i hi, hi⟩⟩
    rw [he, min_eq_right (Finset.card_le_card hsub)]

lemma spectral_label_count_comp {ι A : Type*} [Fintype ι]
    [DecidableEq A] (b : ι → A) (p : Equiv.Perm ι) (v : A) :
    (Finset.univ.filter fun i => b (p i) = v).card =
      (Finset.univ.filter fun i => b i = v).card := by
  classical
  have h := Equiv.sum_comp p (fun i => if b i = v then (1 : ℕ) else 0)
  simpa using h

lemma aligned_changed_count_le {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] (a b : ι → A) (v : A)
    (hp : (∀ i, a i = v → b i = v) ∨ (∀ i, b i = v → a i = v)) :
    ((Finset.univ.filter fun i => a i = v ∧ a i ≠ b i).card : ℝ) ≤
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b i = v).card : ℝ)| := by
  let left := Finset.univ.filter fun i => a i = v
  let both := Finset.univ.filter fun i => a i = v ∧ b i = v
  let diff := Finset.univ.filter fun i => a i = v ∧ a i ≠ b i
  have heq : both.card + diff.card = left.card := by
    have h := Finset.card_filter_add_card_filter_not (s := left) (fun i => b i = v)
    have hpos : left.filter (fun i => b i = v) = both := by
      ext i
      simp only [left, both, Finset.mem_filter, Finset.mem_univ, true_and]
    have hneg : left.filter (fun i => ¬ b i = v) = diff := by
      ext i
      simp only [left, diff, Finset.mem_filter, Finset.mem_univ, true_and]
      aesop
    rw [hpos, hneg] at h
    exact h
  have hboth := spectral_alignment_common_count a b (Equiv.refl ι) v hp
  change both.card = min left.card (Finset.univ.filter fun i => b i = v).card at hboth
  rw [hboth] at heq
  rcases le_total left.card (Finset.univ.filter fun i => b i = v).card with hl | hr
  · rw [min_eq_left hl] at heq
    have hd : diff.card = 0 := by omega
    change (diff.card : ℝ) ≤ _
    rw [hd, Nat.cast_zero]
    exact abs_nonneg _
  · rw [min_eq_right hr] at heq
    have hc : ((Finset.univ.filter fun i => b i = v).card : ℝ) + diff.card = left.card := by
      exact_mod_cast heq
    change (diff.card : ℝ) ≤ |(left.card : ℝ) - _|
    exact (le_abs_self _).trans' (by linarith)

end InvariantIsing

end

end OAI
