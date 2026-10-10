import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchedPrimeRanges

namespace OAI

/-! # A code-changing matching exposes two actual bulk leaves -/
namespace Ostmann
open scoped Classical

theorem scheduled_nonanchor_matching_witness {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (scheduledBulkLabel role n) \
      scheduledAnchorMatchingSet role n m word) :
    ∃ (i i' : I) (t t' : Fin n → Bool) (h : CopyScheduleH role n),
      role i = .word ∧ role i' = .word ∧ h.val = copySchedulePath n t i ∧
      (e.symm h).val = copySchedulePath n t' i' ∧
      finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t' := by
  obtain ⟨hlabel, hn⟩ := Finset.mem_sdiff.mp he
  have hl := (mem_cellPreservingMatchings _ _).mp hlabel
  let e₀ : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n) := ⟨e, hl⟩
  have hncode : ¬ PreservesScheduledAnchorCode role n m word e₀ := by
    intro hc
    exact hn ((mem_scheduledAnchorMatchingSet role n m word e).mpr ⟨hl, hc⟩)
  obtain ⟨x, hx⟩ := not_forall.mp hncode
  let f := separatedMatchingLeft (scheduledSeparatedMatching role n m word e₀)
  let h := (scheduledBulkCoordinates role n m word (f x)).val
  have heh : e.symm h = (scheduledBulkCoordinates role n m word x).val := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (scheduledBulkMatching_slot role n m word e₀ x).symm
  refine ⟨(word (f x).2).val, (word x.2).val,
    scheduledPathEnumeration n (f x).1, scheduledPathEnumeration n x.1,
    h, (word (f x).2).property, (word x.2).property, rfl, ?_, hx⟩
  rw [heh]
  rfl

/-- The prime ranges in either parity case come from the actual changed leaf. -/
theorem scheduled_nonanchor_prime_ranges {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (pivot : ℕ → I) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (he : e ∈ cellPreservingMatchings (scheduledBulkLabel role (n + 1)) \
      scheduledAnchorMatchingSet role (n + 1) m word)
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (Q₀ : I → Finset ℕ)
    (hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
    (hχword : ∀ v, role v = .word → ∀ q ∈ Q₀ v, χ v q ^ 2 ≠ 1)
    (ℓs ℓw : ℝ) (Bs Bw Aw Ew Aa Ea : ℕ)
    (hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
    (hwordrange : ∀ v, role v = .word → ∀ p ∈ Q₀ v,
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
  obtain ⟨i, i', t, t', h, hi, hi', hh, hh', hc⟩ :=
    scheduled_nonanchor_matching_witness role (n + 1) m word e he
  exact scheduled_matched_code_prime_ranges role pivot n e small large hsmall hlarge hp
    i i' hi hi' t t' h hh hh' hc χ Q₀ hχsmall hχword ℓs ℓw Bs Bw Aw Ew Aa Ea
    hsmallrange hwordrange hlargerange

end Ostmann

end OAI
