import OAI.Analysis.IrrationalRotation.Model.CompactTransfer

namespace OAI

open MeasureTheory
open scoped ENNReal NNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem absolutelyContinuous {μ : Measure X} {ν : ι → Measure X}
    (h : UniformlyAbsolutelyContinuous μ ν) (i : ι) : ν i ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  have hsmall : μ s < (δ : ℝ≥0∞) := by
    rw [hzero]
    exact_mod_cast hδ
  simpa only [bot_eq_zero, zero_add] using (hbound s hs hsmall i).le

theorem of_le {μ : Measure X} {ν ρ : ι → Measure X}
    (h : UniformlyAbsolutelyContinuous μ ν) (hle : ∀ i, ρ i ≤ ν i) :
    UniformlyAbsolutelyContinuous μ ρ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  exact ⟨δ, hδ, fun s hs hsmall i => (hle i s).trans_lt (hb s hs hsmall i)⟩

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
