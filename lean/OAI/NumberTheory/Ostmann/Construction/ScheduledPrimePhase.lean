import OAI.NumberTheory.Ostmann.Construction.CopyScheduleUnary
import OAI.NumberTheory.Ostmann.Construction.DirectedPhaseReindex
import OAI.NumberTheory.Ostmann.Construction.CopiedDirectedPhase

namespace OAI

/-! # The directed phase on the actual surviving prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledPrimePhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (p : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ)
    [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p) : ℂ :=
  directedPrimePhase p (fun i => χ (copyScheduleOrigin n i.val) (p i))
    (fun i => center (p i)) (fun i => copyScheduleUnary χ g pivot initial n t i.val (p i))
    (fun i j => copyScheduleGraph g pivot n i.val j.val) (frequencyRoot n t)

theorem copiedSlotCharacter_schedule {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) i =
      χ (copyScheduleOrigin (n + 1) (scheduledOutputVertex role n i).val) := by
  rcases i with ⟨b, h⟩ | y <;> rfl

/-- The copied local phase is exactly the next phase on all surviving slots,
with the same original character attached to every copied prime coordinate. -/
theorem scheduledPrimePhase_step {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (q : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n → ℕ)
    [∀ i, Fact (q i).Prime] (center : ∀ p : ℕ, ZMod p) :
    directedPrimePhase q
      (fun i => copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) i (q i))
      (fun i => center (q i))
      (copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
        (scheduledRetainedGraph role g pivot n)
        (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
        (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
        (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
        (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1)
      (transferredGraph (scheduledRetainedGraph role g pivot n)) t.1 =
    scheduledPrimePhase role χ g pivot initial (n + 1) t
      (fun j => q (copyScheduleSurvivorEquiv role n j)) center := by
  let e := copyScheduleSurvivorEquiv role n
  rw [← directedPrimePhase_equiv e]
  unfold scheduledPrimePhase
  have hout (j : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i}) :
      (scheduledOutputVertex role n (e j)).val = j.val := by
    exact congrArg Subtype.val (e.symm_apply_apply j)
  have hc : (fun j => copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
      (fun y => χ (copyScheduleOrigin n y.val)) (e j) (q (e j))) =
      (fun j => χ (copyScheduleOrigin (n + 1) j.val) (q (e j))) := by
    funext j
    rw [copiedSlotCharacter_schedule, hout]
  have hν : (fun j => copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
      (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 (e j)) =
      (fun j => copyScheduleUnary χ g pivot initial (n + 1) t j.val (q (e j))) := by
    funext j
    rw [copyScheduleUnary_update, hout]
  have hg : (fun i j => transferredGraph (scheduledRetainedGraph role g pivot n) (e i) (e j)) =
      (fun i j => copyScheduleGraph g pivot (n + 1) i.val j.val) := by
    funext i j
    rw [scheduledRetainedGraph_update, hout, hout]
  rw [hc, hν, hg]
  rfl

/-- The copied phase appearing in the exact arithmetic off-diagonal is
already the actual next schedule phase. -/
theorem copiedDirectedPhase_scheduled {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) :
    letI := transferredPrimeFact L R U
    copiedDirectedPhase L R U center
      (fun h => χ (copyScheduleOrigin n h.val))
      (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (L h))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (R h))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (U y))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (U y))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 =
    scheduledPrimePhase role χ g pivot initial (n + 1) t
      (fun j => transferredLabels L R U (copyScheduleSurvivorEquiv role n j)) center := by
  let := transferredPrimeFact L R U
  exact scheduledPrimePhase_step role χ g pivot initial n t (transferredLabels L R U) center

end Ostmann

end OAI
