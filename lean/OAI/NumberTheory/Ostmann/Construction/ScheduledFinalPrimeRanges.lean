import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPairReindex

namespace OAI

/-! # The final one-sided pair retains its actual anchor and word origins -/
namespace Ostmann
open scoped Classical

@[simp] theorem copyScheduleOrigin_outside {I : Type*} (n : ℕ) (i : I) :
    copyScheduleOrigin n (copyScheduleOutside n i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem copyScheduleOrigin_anchor {I : Type*} (n j : ℕ) (b : Bool) (i : I) :
    copyScheduleOrigin n (copyScheduleAnchor n j b i) = i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hj : j = n
    · subst j
      rw [copyScheduleAnchor_new]
      exact copyScheduleOrigin_outside n i
    · rw [copyScheduleAnchor_old n j b i hj]
      exact ih

theorem scheduled_final_pair_interaction_word {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (h : CopyScheduleH role (n + 1)) (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) (scheduledPairMatching role n m word e f)
      role (copyScheduleOrigin (n + 1) h.val) = .word ∧
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨x, hx⟩ := distinct_reassignments_change_code (fun _ => 1)
    (fun _ => Or.inl rfl) e f hef
  let h := scheduledWordH role (n + 1) (parityPathValue (paritySlotPerm e x).1)
    (word (paritySlotPerm e x).2)
  have he : scheduledFinalPerm role n m word e
      (scheduledWordH role (n + 1) (parityPathValue x.1) (word x.2)) = h :=
    scheduledFinalPerm_word role n m word e x
  have hf : (scheduledPairMatching role n m word e f).symm h =
      scheduledWordH role (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (word (paritySlotPerm f x).2) := by
    change scheduledFinalPerm role n m word f ((scheduledFinalPerm role n m word e).symm h) = _
    rw [← he, Equiv.symm_apply_apply]
    exact scheduledFinalPerm_word role n m word f x
  have hpath : ((scheduledPairMatching role n m word e f).symm h).val =
      copySchedulePath (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (word (paritySlotPerm f x).2).val := by
    rw [hf]
    rfl
  have hparity := (paritySlotPerm_preserves_parity e x).trans
    (paritySlotPerm_preserves_parity f x).symm
  obtain ⟨j, b, hj⟩ := scheduledMatchedGraph_changed_code role pivot n
    (scheduledPairMatching role n m word e f) anchor ha hp
    (word (paritySlotPerm e x).2).val (word (paritySlotPerm f x).2).val
    (word (paritySlotPerm e x).2).property (word (paritySlotPerm f x).2).property
    (parityPathValue (paritySlotPerm e x).1) (parityPathValue (paritySlotPerm f x).1)
    h rfl hpath hparity hx
  refine ⟨h, j, b, ?_, hj⟩
  change role (copyScheduleOrigin (n + 1)
    (copySchedulePath (n + 1) (parityPathValue (paritySlotPerm e x).1)
      (word (paritySlotPerm e x).2).val)) = .word
  rw [copyScheduleOrigin_path]
  exact (word (paritySlotPerm e x).2).property

theorem scheduled_final_relative_origins {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (a b : CopyScheduleAtoms role (n + 1)) (j : Fin (n + 1)),
      a ≠ b ∧ copyScheduleOrigin (n + 1) a.val = anchor j ∧
      role (copyScheduleOrigin (n + 1) b.val) = .word ∧
      (let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledFinalRelativePerm role n m word e f)
          (scheduledSurvivorGraph role pivot (n + 1)))
       (G a b = 2 ∨ G a b = -2) ∧ G b a = 0) := by
  have hinv : e⁻¹ ≠ f⁻¹ := fun h => hef (inv_injective h)
  obtain ⟨h, j, sign, hword, hfwd, hrev⟩ :=
    scheduled_final_pair_interaction_word role pivot n m word anchor ha hp (e⁻¹) (f⁻¹) hinv
  refine ⟨scheduledRetainedEmbedding role (n + 1)
    (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign)),
    scheduledRetainedEmbedding role (n + 1) (.inl h), j,
    (scheduledRetainedEmbedding role (n + 1)).injective.ne (by simp), ?_, hword, ?_, ?_⟩
  · exact copyScheduleOrigin_anchor (n + 1) j sign (anchor j)
  · rw [scheduledFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hfwd
  · rw [scheduledFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hrev

/-- The actual one-sided pair lies in the small anchor and long word ranges.
These are the precise prime sets used by the original independent priors. -/
theorem scheduled_final_relative_prime_ranges {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (Q : I → Finset ℕ) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (lower : ℝ) (Bq A E : ℕ)
    (hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
    (hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
    (hword : ∀ i, role i = .word → ∀ p ∈ Q i, 2 * A ≤ p ∧ p ≤ E)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ a b : CopyScheduleAtoms role (n + 1), a ≠ b ∧
      (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val), lower ≤ (q : ℝ) ∧ q ≤ Bq) ∧
      (∀ p ∈ Q (copyScheduleOrigin (n + 1) b.val), 2 * A ≤ p ∧ p ≤ E) ∧
      (let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledFinalRelativePerm role n m word e f)
          (scheduledSurvivorGraph role pivot (n + 1)))
       (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val),
         χ (copyScheduleOrigin (n + 1) a.val) q ^ G a b ≠ 1) ∧ G b a = 0) := by
  obtain ⟨a, b, j, hab, haorig, hbword, hfwd, hrev⟩ :=
    scheduled_final_relative_origins role pivot n m word anchor ha hp e f hef
  refine ⟨a, b, hab, ?_, hword _ hbword, ?_, hrev⟩
  · rw [haorig]
    exact hanchor j
  · intro q hq
    apply signed_square_nonprincipal _ _ _ hfwd
    rw [haorig] at hq ⊢
    exact hsquare j q hq

end Ostmann

end OAI
