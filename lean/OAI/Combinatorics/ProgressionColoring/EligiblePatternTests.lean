import OAI.Combinatorics.ProgressionColoring.EligibleRecordedSupport
import OAI.Combinatorics.ProgressionColoring.AnchoredPatterns
import Mathlib.Data.Fintype.Sigma

namespace OAI

/-!
# Actual tests from eligible return-period patterns

The index records the period and the literal pair of rational step and recorded
word. Realizing parameters are existential witnesses, not extra test indices.
Incidence with a label is exactly the anchored family `AnchoredPatterns.through`.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.EligiblePatternTests

open AnchoredPatterns

variable {D : ℕ}

/-- Each event keeps its actual period, rational step and recorded word. -/
abbrev TestIndex (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (periods : Finset ℕ) :=
  (h : ↥periods) × ↥(eligiblePairs (D := D) (h := h.val) n hn A eta lambda)

variable {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ}
  {lambda : ℕ} {periods : Finset ℕ}

def period (i : TestIndex (D := D) n hn A eta lambda periods) : ℕ := i.1.val

def step (i : TestIndex (D := D) n hn A eta lambda periods) :
    Fin D → Fin (period i) := i.2.val.1

def word (i : TestIndex (D := D) n hn A eta lambda periods) :
    Fin (period i) → Option (FullLabel D (Fin n) A.Label) := i.2.val.2

/-- Only the actual non-dummy recorded labels are used by an event. -/
def support (i : TestIndex (D := D) n hn A eta lambda periods) :
    Finset (FullLabel D (Fin n) A.Label) := RecordedSupport.support (word i)

theorem period_mem (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ∈ periods := i.1.property

theorem word_eligible (i : TestIndex (D := D) n hn A eta lambda periods) :
    eligibleOptionFullLabel n hn A eta lambda (step i) (word i) :=
  (mem_eligiblePairs n hn A eta lambda i.2.val).mp i.2.property

@[simp] theorem mem_support (i : TestIndex (D := D) n hn A eta lambda periods)
    (beta : FullLabel D (Fin n) A.Label) :
    beta ∈ support i ↔ ∃ z, word i z = some beta :=
  RecordedSupport.mem_support (word i) beta

theorem word_labelsInjective (i : TestIndex (D := D) n hn A eta lambda periods) :
    RecordedSupport.LabelsInjective (word i) :=
  eligibleOptionFullLabel_labelsInjective (word_eligible i)

theorem word_regular_many (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ≤ 2 * (RecordedSupport.regularPositions (word i)).card :=
  eligibleOptionFullLabel_regular_many (word_eligible i)

theorem support_card_eq (i : TestIndex (D := D) n hn A eta lambda periods) :
    (support i).card = (RecordedSupport.regularPositions (word i)).card :=
  RecordedSupport.support_card_eq (word i) (word_labelsInjective i)

theorem period_le_two_support_card
    (i : TestIndex (D := D) n hn A eta lambda periods) :
    period i ≤ 2 * (support i).card := by
  rw [support_card_eq]
  exact word_regular_many i

/-- The actual positions of each balanced color occupy at least an eighth
of the period. -/
theorem period_le_eight_colored
    (i : TestIndex (D := D) n hn A eta lambda periods)
    (color : FullLabel D (Fin n) A.Label → Bool) (b : Bool)
    (hbalance : (support i).card ≤ 4 * ((support i).filter fun beta => color beta = b).card) :
    period i ≤ 8 * (RecordedSupport.coloredPositions (word i) color b).card :=
  RecordedSupport.length_le_eight_colored (word i) (word_labelsInjective i)
    color b (word_regular_many i) hbalance

/-- Incidences in a single period slice of the concrete event index. -/
def incidentSlice (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (periods : Finset ℕ) (h : ℕ)
    (beta : FullLabel D (Fin n) A.Label) :
    Finset (TestIndex (D := D) n hn A eta lambda periods) := by
  classical
  exact Finset.univ.filter fun i => period i = h ∧ beta ∈ support i

@[simp] theorem mem_incidentSlice (h : ℕ) (beta : FullLabel D (Fin n) A.Label)
    (i : TestIndex (D := D) n hn A eta lambda periods) :
    i ∈ incidentSlice n hn A eta lambda periods h beta ↔
      period i = h ∧ beta ∈ support i := by
  classical
  simp [incidentSlice]

theorem incidentSlice_card_eq_through (h : ℕ) (hh : h ∈ periods)
    (beta : FullLabel D (Fin n) A.Label) :
    (incidentSlice n hn A eta lambda periods h beta).card =
      (through (h := h) n hn A eta lambda beta).card := by
  classical
  symm
  let tag : ∀ p ∈ through (h := h) n hn A eta lambda beta,
      TestIndex (D := D) n hn A eta lambda periods := fun p hp =>
    ⟨⟨h, hh⟩, ⟨p, (mem_eligiblePairs n hn A eta lambda p).mpr
      ((mem_through n hn A eta lambda beta p).mp hp).1⟩⟩
  apply Finset.card_bij tag
  · intro p hp
    apply (mem_incidentSlice h beta (tag p hp)).mpr
    refine ⟨rfl, ?_⟩
    exact (mem_support (tag p hp) beta).mpr
      ((mem_through n hn A eta lambda beta p).mp hp).2
  · intro p hp q hq hpq
    dsimp only [tag] at hpq
    have hsub := sigma_mk_injective (α := ↥periods)
      (β := fun j : ↥periods =>
        ↥(eligiblePairs (D := D) (h := j.val) n hn A eta lambda))
      (i := ⟨h, hh⟩) hpq
    exact congrArg Subtype.val hsub
  · rintro ⟨⟨h', hh'⟩, ⟨p, hp⟩⟩ hi
    have hi' := (mem_incidentSlice h beta _).mp hi
    change h' = h ∧ beta ∈ RecordedSupport.support p.2 at hi'
    obtain ⟨heq, hbeta⟩ := hi'
    subst h'
    have hp' : p ∈ through (h := h) n hn A eta lambda beta :=
      (mem_through n hn A eta lambda beta p).mpr
        ⟨(mem_eligiblePairs n hn A eta lambda p).mp hp,
          (RecordedSupport.mem_support p.2 beta).mp hbeta⟩
    exact ⟨p, hp', rfl⟩

theorem incidentSlice_eq_empty_of_not_mem (h : ℕ) (hh : h ∉ periods)
    (beta : FullLabel D (Fin n) A.Label) :
    incidentSlice n hn A eta lambda periods h beta = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hih := ((mem_incidentSlice h beta i).mp hi).1
  exact hh (hih ▸ period_mem i)

/-- A bound on canonical anchored pairs applies to the incident slice at every
natural period, including periods outside the finite family. -/
theorem incident_card_le_of_through (countBound : ℕ → ℕ)
    (hcount : ∀ h ∈ periods, ∀ beta : FullLabel D (Fin n) A.Label,
      (through (h := h) n hn A eta lambda beta).card ≤ countBound h)
    (beta : FullLabel D (Fin n) A.Label) (h : ℕ) :
    (Finset.univ.filter (fun i : TestIndex (D := D) n hn A eta lambda periods =>
      beta ∈ support i ∧ period i = h)).card ≤ countBound h := by
  classical
  have hslice : (Finset.univ.filter
      (fun i : TestIndex (D := D) n hn A eta lambda periods =>
        beta ∈ support i ∧ period i = h)) =
      incidentSlice n hn A eta lambda periods h beta := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_incidentSlice,
      and_comm]
  rw [hslice]
  by_cases hh : h ∈ periods
  · rw [incidentSlice_card_eq_through h hh beta]
    exact hcount h hh beta
  · rw [incidentSlice_eq_empty_of_not_mem h hh beta, Finset.card_empty]
    exact Nat.zero_le _

/-- The proved geometric anchored bound applies directly to the actual second
family of outer-coloring events. -/
theorem incident_card_le (hD : 0 < D)
    (hperiods : ∀ h ∈ periods, 0 < h)
    (beta : FullLabel D (Fin n) A.Label) (h : ℕ) :
    (Finset.univ.filter (fun i : TestIndex (D := D) n hn A
        (1 / (1000 * (D : ℝ))) lambda periods =>
      beta ∈ support i ∧ period i = h)).card ≤ (16005 * D * h) ^ (14 * D) := by
  apply incident_card_le_of_through (fun h => (16005 * D * h) ^ (14 * D))
  intro h hh beta
  exact card_through_le n hn A lambda beta hD (hperiods h hh)

end QuantitativeVanDerWaerden.EligiblePatternTests

end

end OAI
