import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection

theorem norm_finset_sum_le_complement
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0) :
    ‖∑ i ∈ s, c i‖ ≤ ∑' i : ↑((s : Set ι)ᶜ), ‖c i‖ := by
  have hsplit := hc.of_norm.sum_add_tsum_compl (s := s)
  rw [hz] at hsplit
  have heq : (∑ i ∈ s, c i) = -(∑' i : ↑((s : Set ι)ᶜ), c i) := by
    simpa using eq_neg_of_add_eq_zero_left hsplit
  rw [heq, norm_neg]
  exact norm_tsum_le_tsum_norm (hc.subtype fun i => i ∈ (s : Set ι)ᶜ)

theorem norm_finset_sum_le_two_tails
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w e₁ e₂ : ι → ℝ) (η : ℝ)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0)
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) (hη : 0 ≤ η)
    (h₁ : ∀ i, 0 ≤ e₁ i ∧ e₁ i ≤ w i) (h₂ : ∀ i, 0 ≤ e₂ i ∧ e₂ i ≤ w i)
    (hb : ∀ i, i ∉ s → ‖c i‖ ≤ η * w i + e₁ i + e₂ i) :
    ‖∑ i ∈ s, c i‖ ≤ η * (∑' i, w i) +
      (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
  have hs₁ : Summable e₁ := Summable.of_nonneg_of_le
    (fun i => (h₁ i).1) (fun i => (h₁ i).2) hw
  have hs₂ : Summable e₂ := Summable.of_nonneg_of_le
    (fun i => (h₂ i).1) (fun i => (h₂ i).2) hw
  have hwc := hw.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have h₁c := hs₁.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have h₂c := hs₂.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have hct := hc.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  simp only [Function.comp_def] at hwc h₁c h₂c hct
  have htail : (∑' i : ↑((s : Set ι)ᶜ), ‖c i‖) ≤
      ∑' i : ↑((s : Set ι)ᶜ), (η * w i + e₁ i + e₂ i) :=
    Summable.tsum_le_tsum (fun i => hb i i.property) hct
      (((hwc.mul_left η).add h₁c).add h₂c)
  have hwle : (∑' i : ↑((s : Set ι)ᶜ), w i) ≤ ∑' i, w i := by
    have hsplit := hw.sum_add_tsum_compl (s := s)
    have hsum : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i hi => hw0 i
    simpa using (le_add_of_nonneg_left hsum).trans_eq hsplit
  calc
    ‖∑ i ∈ s, c i‖ ≤ ∑' i : ↑((s : Set ι)ᶜ), ‖c i‖ :=
      norm_finset_sum_le_complement s c hc hz
    _ ≤ ∑' i : ↑((s : Set ι)ᶜ), (η * w i + e₁ i + e₂ i) := htail
    _ = η * (∑' i : ↑((s : Set ι)ᶜ), w i) +
        (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
      rw [((hwc.mul_left η).add h₁c).tsum_add h₂c, (hwc.mul_left η).tsum_add h₁c,
        tsum_mul_left]
    _ ≤ η * (∑' i, w i) +
        (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
      gcongr

theorem norm_finset_sum_le_masked_tail
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℝ) (η : ℝ)
    (H₁ H₂ : Set ι)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0)
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) (hη : 0 ≤ η)
    (hb : ∀ i, i ∉ s → ‖c i‖ ≤
      (η + H₁.indicator (fun _ => (1 : ℝ)) i +
        H₂.indicator (fun _ => (1 : ℝ)) i) * w i) :
    ‖∑ i ∈ s, c i‖ ≤ η * (∑' i, w i) +
      (∑' i : ↑((s : Set ι)ᶜ), H₁.indicator w i) +
      (∑' i : ↑((s : Set ι)ᶜ), H₂.indicator w i) := by
  classical
  apply norm_finset_sum_le_two_tails s c w (H₁.indicator w) (H₂.indicator w)
    η hc hz hw hw0 hη
  · intro i
    by_cases hi : i ∈ H₁ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hw0 i]
  · intro i
    by_cases hi : i ∈ H₂ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hw0 i]
  · intro i hi
    convert hb i hi using 1
    simp only [Set.indicator_apply]
    split_ifs <;> ring

theorem omitted_index_selector (K n v : ℤ)
    (h : ¬ (|v| ≤ K ∧ |n + v| ≤ K)) :
    K < |if K < |v| then v else n + v| := by
  split_ifs with hv
  · exact hv
  · have hv' : |v| ≤ K := le_of_not_gt hv
    exact lt_of_not_ge (fun hn => h ⟨hv', hn⟩)

theorem omitted_index_ratio_bound (K n v : ℤ) (R : ℤ → ℝ) (r : ℝ)
    (hr : r ≤ min (R v) (R (n + v))) :
    r ≤ R (if K < |v| then v else n + v) := by
  split_ifs
  · exact hr.trans (min_le_left _ _)
  · exact hr.trans (min_le_right _ _)

end InvariantProjection

end OAI
