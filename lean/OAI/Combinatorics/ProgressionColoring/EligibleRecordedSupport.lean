import OAI.Combinatorics.ProgressionColoring.AnchoredPatternDefinitions
import OAI.Combinatorics.ProgressionColoring.RecordedSupport

namespace OAI

/-!
# Eligibility of literal recorded supports

The recorded-word mask agrees exactly with geometric regularity. Consequently,
the injectivity and density clauses of geometric eligibility provide the
hypotheses used when transferring support balancing to actual positions.
-/

namespace QuantitativeVanDerWaerden.AnchoredPatterns

variable {D h : ℕ}

theorem recordedWord_ne_none_iff (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h) :
    recordedWord n hn A eta R lambda t z ≠ none ↔ regular eta R lambda t z := by
  rw [Option.ne_none_iff_exists']
  constructor
  · rintro ⟨β, hβ⟩
    exact ((recordedWord_eq_some_iff n hn A eta R lambda t z β).mp hβ).1
  · intro hz
    refine ⟨fullLabel n hn A R lambda t z, ?_⟩
    exact (recordedWord_eq_some_iff n hn A eta R lambda t z _).mpr ⟨hz, rfl⟩

/-- The literal mask and geometric regularity select the same positions. -/
theorem recordedWord_regularPositions_eq (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    RecordedSupport.regularPositions (recordedWord n hn A eta R lambda t) =
      regularPositions eta R lambda t := by
  classical
  ext z
  simp only [RecordedSupport.mem_regularPositions, recordedWord_ne_none_iff,
    regularPositions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Geometric injectivity gives uniqueness of every recorded full label. -/
theorem EligibleRealization.recordedWord_labelsInjective
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {R : Realization D}
    (hR : EligibleRealization n hn A eta lambda t R) :
    RecordedSupport.LabelsInjective (recordedWord n hn A eta R lambda t) := by
  intro z z' β hz hz'
  obtain ⟨hzreg, hzlabel⟩ :=
    (recordedWord_eq_some_iff n hn A eta R lambda t z β).mp hz
  obtain ⟨hz'reg, hz'label⟩ :=
    (recordedWord_eq_some_iff n hn A eta R lambda t z' β).mp hz'
  exact hR.regular_injective z z' hzreg hz'reg (hzlabel.trans hz'label.symm)

/-- The eligibility density condition is a literal recorded-position bound. -/
theorem EligibleRealization.recordedWord_regular_many
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {R : Realization D}
    (hR : EligibleRealization n hn A eta lambda t R) :
    h ≤ 2 * (RecordedSupport.regularPositions
      (recordedWord n hn A eta R lambda t)).card := by
  rw [recordedWord_regularPositions_eq]
  exact hR.regular_many

/-- Recorded-label uniqueness depends only on the eligible word, regardless
of which eligible realization witnesses it. -/
theorem eligibleOptionFullLabel_labelsInjective
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {word : Fin h → Option (FullLabel D (Fin n) A.Label)}
    (hword : eligibleOptionFullLabel n hn A eta lambda t word) :
    RecordedSupport.LabelsInjective word := by
  obtain ⟨R, hR, hrecorded⟩ := hword
  rw [← hrecorded]
  exact hR.recordedWord_labelsInjective

/-- At least half the positions of every eligible word carry a literal label. -/
theorem eligibleOptionFullLabel_regular_many
    {n : ℕ} {hn : 0 < n} {A : AdaptiveMesh} {eta : ℝ} {lambda : ℕ}
    {t : Fin D → Fin h} {word : Fin h → Option (FullLabel D (Fin n) A.Label)}
    (hword : eligibleOptionFullLabel n hn A eta lambda t word) :
    h ≤ 2 * (RecordedSupport.regularPositions word).card := by
  obtain ⟨R, hR, hrecorded⟩ := hword
  rw [← hrecorded]
  exact hR.recordedWord_regular_many

end QuantitativeVanDerWaerden.AnchoredPatterns

end OAI
