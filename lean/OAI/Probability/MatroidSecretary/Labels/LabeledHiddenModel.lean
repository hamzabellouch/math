import OAI.Probability.MatroidSecretary.Labels.FiniteLabelingModel

namespace OAI

namespace MatroidProphet.Labeling

open Finset

/-- A hidden rule on arbitrary finite labels has the same online information
restriction as the canonical `Fin n` hidden rule. -/
structure LabeledHiddenRule (E : Type*) [Fintype E] [MeasurableSpace E]
    (bits : ℕ) where
  mask : Seed bits → Finset E
  core : LabeledOnlineRule E bits

noncomputable def labeledObserved {E : Type*} [Fintype E] [MeasurableSpace E]
    {bits : ℕ} (A : LabeledHiddenRule E bits) (r : Seed bits) (w : E → ℝ) :
    E → ℝ := by
  classical
  exact fun e => if e ∈ A.mask r then w e else 0

noncomputable def labeledHiddenAcceptedThrough
    {E : Type*} [Fintype E] [MeasurableSpace E] {bits : ℕ}
    (A : LabeledHiddenRule E bits) (r : Seed bits) (w : E → ℝ)
    (π : LabeledOrder E) (t : ℕ) : Finset E := by
  classical
  exact labeledAcceptedThrough A.core r (labeledObserved A r w) w π t \ A.mask r

noncomputable def labeledHiddenReward
    {E : Type*} [Fintype E] [MeasurableSpace E] {bits : ℕ}
    (A : LabeledHiddenRule E bits) (r : Seed bits) (w : E → ℝ)
    (π : LabeledOrder E) : ℝ :=
  ∑ e ∈ labeledHiddenAcceptedThrough A r w π (Fintype.card E), w e

noncomputable def labeledHiddenWorstReward
    {E : Type*} [Fintype E] [MeasurableSpace E] {bits : ℕ}
    (A : LabeledHiddenRule E bits) (w : E → ℝ) (r : Seed bits) : ℝ := by
  classical
  exact Finset.univ.inf' ⟨(Fintype.equivFin E).symm, mem_univ _⟩
    (labeledHiddenReward A r w)

end MatroidProphet.Labeling

end OAI
