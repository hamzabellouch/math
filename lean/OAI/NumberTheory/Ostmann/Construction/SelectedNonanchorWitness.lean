import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchedPrimeRanges

namespace OAI

/-! # One-sided interactions at the actual selected bulk primes -/
namespace Ostmann
open scoped Classical

theorem scheduled_matched_code_prime_ranges_at {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t')
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (Q₀ : I → Finset ℕ)
    (hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
    (hχword : ∀ q ∈ Q₀ i, χ i q ^ 2 ≠ 1)
    (ℓs ℓw : ℝ) (Bs Bw Aw Ew Aa Ea : ℕ)
    (hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
    (hwordrange : ∀ p ∈ Q₀ i,
      (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
    (hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea) :
    let χR := scheduledRetainedCharacters role χ (n + 1)
    let Q := Sum.elim (fun h : CopyScheduleH role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y : CopyScheduleY role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let G := scheduledMatchedGraph role pivot (n + 1) e
    ∃ a b : CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1),
      a ≠ b ∧ (G a a = 0 ∧ G b b = 0) ∧ G b a = 0 ∧
      (∀ q ∈ Q a, χR a q ^ G a b ≠ 1) ∧
      (((∀ q ∈ Q a, ℓs ≤ (q : ℝ) ∧ q ≤ Bs) ∧ (∀ p ∈ Q b, 2 * Aw ≤ p ∧ p ≤ Ew)) ∨
       ((∀ q ∈ Q a, ℓw ≤ (q : ℝ) ∧ q ≤ Bw) ∧ (∀ p ∈ Q b, 2 * Aa ≤ p ∧ p ≤ Ea))) := by
  intro χR Q G
  obtain ⟨j, sign, hedge⟩ := scheduledMatchedGraph_changed_code_split role pivot n e small large
    hsmall hlarge hp i i' hi hi' t t' h hh hh' hcode
  let a := scheduledPastAnchor role n (small j) j (hsmall j) sign
  let a' := scheduledPastAnchor role n (large j) j (hlarge j) sign
  have hwo : copyScheduleOrigin (n + 1) h.val = i := by rw [hh, copyScheduleOrigin_path]
  have hQs : Q (.inr a) = Q₀ (small j) := by
    change Q₀ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (small j))) = _
    rw [copyScheduleOrigin_anchor]
  have hQa : Q (.inr a') = Q₀ (large j) := by
    change Q₀ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (large j))) = _
    rw [copyScheduleOrigin_anchor]
  have hQw : Q (.inl h) = Q₀ i := by change Q₀ (copyScheduleOrigin (n + 1) h.val) = _; rw [hwo]
  have hχs : χR (.inr a) = χ (small j) := by
    change χ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (small j))) = _
    rw [copyScheduleOrigin_anchor]
  have hχw : χR (.inl h) = χ i := by change χ (copyScheduleOrigin (n + 1) h.val) = _; rw [hwo]
  rcases hedge with hedge | hedge
  · refine ⟨.inr a, .inl h, by simp, ⟨scheduledMatchedGraph_self _ _ _ _ _,
        scheduledMatchedGraph_self _ _ _ _ _⟩, hedge.2, ?_, Or.inl ?_⟩
    · intro q hq
      rw [hχs]
      exact signed_square_nonprincipal _ (hχsmall j q (hQs ▸ hq)) _ hedge.1
    · constructor
      · rw [hQs]
        exact hsmallrange j
      · rw [hQw]
        exact fun p hp => (hwordrange p hp).2
  · refine ⟨.inl h, .inr a', by simp, ⟨scheduledMatchedGraph_self _ _ _ _ _,
        scheduledMatchedGraph_self _ _ _ _ _⟩, hedge.2, ?_, Or.inr ?_⟩
    · intro q hq
      rw [hχw]
      exact signed_square_nonprincipal _ (hχword q (hQw ▸ hq)) _ hedge.1
    · constructor
      · rw [hQw]
        exact fun p hp => (hwordrange p hp).1
      · rw [hQa]
        exact hlargerange j

theorem selected_nonanchor_matching_witness {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk) :
    ∃ (i i' : Fin m) (t t' : Fin n → Bool) (h : CopyScheduleH role n),
      h.val = copySchedulePath n t (bulk i) ∧
      (e.symm h).val = copySchedulePath n t' (bulk i') ∧
      finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t' := by
  obtain ⟨hlabel, hn⟩ := Finset.mem_sdiff.mp he
  have hl := (mem_cellPreservingMatchings _ _).mp hlabel
  let e₀ : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk) := ⟨e, hl⟩
  have hncode : ¬ PreservesSelectedAnchorCode role n m bulk hbulk e₀ := by
    intro hc
    exact hn ((mem_selectedAnchorMatchingSet role n m bulk hbulk e).mpr ⟨hl, hc⟩)
  obtain ⟨x, hx⟩ := not_forall.mp hncode
  let f := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e₀)
  let h := selectedBulkH role n m bulk hbulk (f x)
  have heh : e.symm h = selectedBulkH role n m bulk hbulk x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (selectedBulkMatching_slot role n m bulk hbulk e₀ x).symm
  refine ⟨(f x).2, x.2, scheduledPathEnumeration n (f x).1,
    scheduledPathEnumeration n x.1, h, rfl, ?_, hx⟩
  rw [heh]
  rfl

/-- The only word-prime range used is that of the selected bulk embedding.
In particular no separation premise is imposed on the top label. -/
theorem selected_nonanchor_prime_ranges {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (pivot : ℕ → I) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role (n + 1) m bulk hbulk) \
      selectedAnchorMatchingSet role (n + 1) m bulk hbulk)
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (Q₀ : I → Finset ℕ)
    (hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
    (hχbulk : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
    (ℓs ℓw : ℝ) (Bs Bw Aw Ew Aa Ea : ℕ)
    (hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
    (hbulkrange : ∀ i p, p ∈ Q₀ (bulk i) →
      (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
    (hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea) :
    let χR := scheduledRetainedCharacters role χ (n + 1)
    let Q := Sum.elim (fun h : CopyScheduleH role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y : CopyScheduleY role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let G := scheduledMatchedGraph role pivot (n + 1) e
    ∃ a b : CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1),
      a ≠ b ∧ (G a a = 0 ∧ G b b = 0) ∧ G b a = 0 ∧
      (∀ q ∈ Q a, χR a q ^ G a b ≠ 1) ∧
      (((∀ q ∈ Q a, ℓs ≤ (q : ℝ) ∧ q ≤ Bs) ∧ (∀ p ∈ Q b, 2 * Aw ≤ p ∧ p ≤ Ew)) ∨
       ((∀ q ∈ Q a, ℓw ≤ (q : ℝ) ∧ q ≤ Bw) ∧ (∀ p ∈ Q b, 2 * Aa ≤ p ∧ p ≤ Ea))) := by
  obtain ⟨i, i', t, t', h, hh, hh', hc⟩ :=
    selected_nonanchor_matching_witness role (n + 1) m bulk hbulk e he
  exact scheduled_matched_code_prime_ranges_at role pivot n e small large hsmall hlarge hp
    (bulk i) (bulk i') (hbulk i) (hbulk i') t t' h hh hh' hc χ Q₀ hχsmall (hχbulk i)
    ℓs ℓw Bs Bw Aw Ew Aa Ea hsmallrange (hbulkrange i) hlargerange

end Ostmann

end OAI
