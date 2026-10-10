import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveVariationEquality

namespace OAI

/-! # Ordered signs with constant positive count are constant -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

/-- A finite set of signs cannot change when every positive sign can only
disappear and their total count stays constant. -/
theorem positive_signs_eq_of_ordered
    {I : Type*} [Fintype I] (q : I → ℝ → ℝ) (τ : I → ℝ)
    {s t : ℝ} (hst : s ≤ t)
    (hs : ∀ i, q i s ≠ 0 ∧ (s ≤ τ i → 0 ≤ q i s) ∧ (τ i < s → q i s ≤ 0))
    (ht : ∀ i, q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0))
    (hcard : (Finset.univ.filter (fun i => 0 < q i s)).card =
      (Finset.univ.filter (fun i => 0 < q i t)).card) :
    ∀ i, (0 < q i s ↔ 0 < q i t) := by
  classical
  have hsub : Finset.univ.filter (fun i => 0 < q i t) ⊆
      Finset.univ.filter (fun i => 0 < q i s) := by
    intro i hi
    have hpos := (Finset.mem_filter.mp hi).2
    have htτ : t ≤ τ i := by
      by_contra hn
      exact (not_lt_of_ge ((ht i).2.2 (lt_of_not_ge hn))) hpos
    have hnonneg := (hs i).2.1 (hst.trans htτ)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      lt_of_le_of_ne hnonneg (Ne.symm (hs i).1)⟩
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.le
  intro i
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (show i ∈ Finset.univ.filter (fun i => 0 < q i s) ↔
      i ∈ Finset.univ.filter (fun i => 0 < q i t) by rw [heq])

/-- The almost-everywhere version needed for the scalar derivatives of a
profile. No monotonicity of the label itself is assumed. -/
theorem exists_constant_positive_signs
    {I : Type*} [Fintype I] (q : I → ℝ → ℝ) (τ : I → ℝ)
    {a b : ℝ} (n : ℕ)
    (hnonzero : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc a b), q i t ≠ 0)
    (hleft : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc a (τ i)), 0 ≤ q i t)
    (hright : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc (τ i) b), q i t ≤ 0)
    (hcard : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (Finset.univ.filter (fun i => 0 < q i t)).card = n) :
    ∃ S : Finset I, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ i, (0 < q i t ↔ i ∈ S) := by
  classical
  let μ := volume.restrict (Ioc a b)
  have hsign (i : I) : ∀ᵐ t ∂μ,
      q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0) := by
    filter_upwards [hnonzero i, ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (ae_imp_of_ae_restrict (hleft i)),
      ae_restrict_of_ae (ae_imp_of_ae_restrict (hright i))] with t ht hmem hl hr
    exact ⟨ht, fun h => hl ⟨hmem.1, h⟩, fun h => hr ⟨h, hmem.2⟩⟩
  have hgood : ∀ᵐ t ∂μ,
      (∀ i, q i t ≠ 0 ∧ (t ≤ τ i → 0 ≤ q i t) ∧ (τ i < t → q i t ≤ 0)) ∧
      (Finset.univ.filter (fun i => 0 < q i t)).card = n :=
    ((ae_all_iff).mpr hsign).and hcard
  by_cases hμ : μ = 0
  · refine ⟨∅, ?_⟩
    change ∀ᵐ t ∂μ, _
    rw [hμ]
    simp
  · have : NeZero μ := ⟨hμ⟩
    obtain ⟨s, hs⟩ := hgood.exists
    refine ⟨Finset.univ.filter (fun i => 0 < q i s), ?_⟩
    filter_upwards [hgood] with t ht
    have heq : ∀ i, 0 < q i s ↔ 0 < q i t := by
      rcases le_total s t with hst | hts
      · exact positive_signs_eq_of_ordered q τ hst hs.1 ht.1 (hs.2.trans ht.2.symm)
      · exact fun i => (positive_signs_eq_of_ordered q τ hts ht.1 hs.1
          (ht.2.trans hs.2.symm) i).symm
    intro i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (heq i).symm

end PolycyclicRecognition

end

end OAI
