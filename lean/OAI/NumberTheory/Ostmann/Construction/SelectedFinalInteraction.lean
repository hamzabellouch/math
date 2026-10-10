import OAI.NumberTheory.Ostmann.Construction.SelectedFullFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.ScheduledFullMatchingGraph
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPrimeRanges

namespace OAI

/-! # A moved selected-bulk slot gives the final one-sided interaction -/
namespace Ostmann
open scoped Classical

noncomputable def selectedPairMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  (selectedFinalPerm role n m bulk hbulk f).symm.trans (selectedFinalPerm role n m bulk hbulk e)

theorem selected_final_pair_interaction {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (h : CopyScheduleH role (n + 1)) (j : Fin (n + 1)) (b : Bool) (i : Fin m),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) (selectedPairMatching role n m bulk hbulk e f)
      copyScheduleOrigin (n + 1) h.val = bulk i ∧
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨x, hx⟩ := distinct_reassignments_change_code (fun _ => 1)
    (fun _ => Or.inl rfl) e f hef
  let h := selectedParityH role n m bulk hbulk (paritySlotPerm e x)
  have he : selectedFinalPerm role n m bulk hbulk e (selectedParityH role n m bulk hbulk x) = h :=
    selectedFinalPerm_bulk role n m bulk hbulk e x
  have hf : (selectedPairMatching role n m bulk hbulk e f).symm h =
      selectedParityH role n m bulk hbulk (paritySlotPerm f x) := by
    change selectedFinalPerm role n m bulk hbulk f ((selectedFinalPerm role n m bulk hbulk e).symm h) = _
    rw [← he, Equiv.symm_apply_apply]
    exact selectedFinalPerm_bulk role n m bulk hbulk f x
  have hpath : ((selectedPairMatching role n m bulk hbulk e f).symm h).val =
      copySchedulePath (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (bulk (paritySlotPerm f x).2) := by
    rw [hf]
    rfl
  have hparity := (paritySlotPerm_preserves_parity e x).trans
    (paritySlotPerm_preserves_parity f x).symm
  obtain ⟨j, b, hj⟩ := scheduledMatchedGraph_changed_code role pivot n
    (selectedPairMatching role n m bulk hbulk e f) anchor ha hp
    (bulk (paritySlotPerm e x).2) (bulk (paritySlotPerm f x).2)
    (hbulk (paritySlotPerm e x).2) (hbulk (paritySlotPerm f x).2)
    (parityPathValue (paritySlotPerm e x).1) (parityPathValue (paritySlotPerm f x).1)
    h rfl hpath hparity hx
  refine ⟨h, j, b, (paritySlotPerm e x).2, ?_, hj⟩
  exact copyScheduleOrigin_path (n + 1) _ _

theorem selectedFinalPerm_inv {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) :
    selectedFinalPerm role n m bulk hbulk (e⁻¹) = (selectedFinalPerm role n m bulk hbulk e).symm := by
  unfold selectedFinalPerm
  rw [paritySlotPerm_inv]
  rfl

noncomputable def selectedFinalRelativePerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  (selectedFullFinalPerm role n m bulk hbulk f).trans (selectedFullFinalPerm role n m bulk hbulk e).symm

theorem selectedFinalRelativePerm_matching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) :
    selectedFinalRelativePerm role n m bulk hbulk e f =
      scheduledHMatching role (n + 1) (selectedPairMatching role n m bulk hbulk (e⁻¹) (f⁻¹)) := by
  change (scheduledHMatching role (n + 1) (selectedFinalPerm role n m bulk hbulk f)).trans
    (scheduledHMatching role (n + 1) (selectedFinalPerm role n m bulk hbulk e)).symm = _
  rw [scheduledHMatching_symm, scheduledHMatching_trans]
  unfold selectedPairMatching
  rw [selectedFinalPerm_inv, selectedFinalPerm_inv, Equiv.symm_symm]

/-- The long prime is certified to be a selected bulk prime, so no upper
prime-range hypothesis is imposed on the top slot. -/
theorem selected_final_relative_prime_ranges {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (Q : I → Finset ℕ) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (lower : ℝ) (Bq A E : ℕ)
    (hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
    (hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
    (hword : ∀ i p, p ∈ Q (bulk i) → 2 * A ≤ p ∧ p ≤ E)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ a b : CopyScheduleAtoms role (n + 1), a ≠ b ∧
      (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val), lower ≤ (q : ℝ) ∧ q ≤ Bq) ∧
      (∀ p ∈ Q (copyScheduleOrigin (n + 1) b.val), 2 * A ≤ p ∧ p ≤ E) ∧
      (let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (selectedFinalRelativePerm role n m bulk hbulk e f)
          (scheduledSurvivorGraph role pivot (n + 1)))
       (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val),
         χ (copyScheduleOrigin (n + 1) a.val) q ^ G a b ≠ 1) ∧ G b a = 0) := by
  have hinv : e⁻¹ ≠ f⁻¹ := fun h => hef (inv_injective h)
  obtain ⟨h, j, sign, i, horig, hfwd, hrev⟩ :=
    selected_final_pair_interaction role pivot n m bulk hbulk anchor ha hp (e⁻¹) (f⁻¹) hinv
  let a := scheduledRetainedEmbedding role (n + 1)
    (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign))
  let b := scheduledRetainedEmbedding role (n + 1) (.inl h)
  have haorig : copyScheduleOrigin (n + 1) a.val = anchor j :=
    copyScheduleOrigin_anchor (n + 1) j sign (anchor j)
  have hborig : copyScheduleOrigin (n + 1) b.val = bulk i := horig
  refine ⟨a, b, (scheduledRetainedEmbedding role (n + 1)).injective.ne (by simp), ?_, ?_, ?_, ?_⟩
  · rw [haorig]
    exact hanchor j
  · rw [hborig]
    exact hword i
  · intro q hq
    rw [selectedFinalRelativePerm_matching, scheduledHMatching_graph]
    apply signed_square_nonprincipal _ _ _ hfwd
    rw [haorig] at hq ⊢
    exact hsquare j q hq
  · rw [selectedFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hrev

end Ostmann

end OAI
