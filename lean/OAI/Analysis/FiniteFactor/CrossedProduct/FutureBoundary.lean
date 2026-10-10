import OAI.Analysis.FiniteFactor.CrossedProduct.BoundaryEvent
import OAI.Analysis.FiniteFactor.Coupling.CoordinateMass

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceBiasedCoordinate_measure (j : ℕ) (i : SourceCoordinate)
    (S : Set (Fin 6 × (ℝ × ℝ))) (hS : MeasurableSet S) :
    (sourceBiasedLaw j) ((fun ω : SourceBiasedSample => ω i) ⁻¹' S) =
      (stagedCouplingParameters j i.1).labelledCoupling S := by
  have hm : Measurable (fun ω : SourceBiasedSample => ω i) := measurable_pi_apply i
  rw [← Measure.map_apply hm hS]
  have he : (sourceBiasedLaw j).map (fun ω => ω i) = (stagedCouplingParameters j i.1).labelledCoupling :=
    Measure.infinitePi_map_eval _ _
  rw [he]

def sourceFutureBad (j n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) : Set SourceBiasedSample :=
  {ω | 1-sourceExclusionWidth j ⟨j+1+n,i⟩ ≤ (ω ⟨j+1+n,i⟩).2.1 ∨
    (ω ⟨j+1+n,i⟩).2.2 ≤ sourceExclusionWidth j ⟨j+1+n,i⟩}

def sourceFutureBoundaryEvent (j : ℕ) : Set SourceBiasedSample :=
  (⋃ n : ℕ, ⋃ i : Fin (sourceBlockSize (j+1+n)), sourceFutureBad j n i)ᶜ

theorem sourceFutureBad_measurable (j n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) :
    MeasurableSet (sourceFutureBad j n i) := by
  have hm : Measurable (fun ω : SourceBiasedSample => ω ⟨j+1+n,i⟩) := measurable_pi_apply _
  exact (measurableSet_le measurable_const (measurable_fst.comp (measurable_snd.comp hm))).union
    (measurableSet_le (measurable_snd.comp (measurable_snd.comp hm)) measurable_const)

theorem sourceFutureBoundaryEvent_measurable (j : ℕ) : MeasurableSet (sourceFutureBoundaryEvent j) :=
  (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun i => sourceFutureBad_measurable j n i).compl

/-- The actual one-coordinate contribution to the future union loss. -/
theorem sourceFutureBad_bound (j n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) :
    (sourceBiasedLaw j) (sourceFutureBad j n i) ≤
      ENNReal.ofReal (20*sourceExclusionWidth j ⟨j+1+n,i⟩) := by
  let a := sourceExclusionWidth j ⟨j+1+n,i⟩
  let p := stagedCouplingParameters j (j+1+n)
  have ha : 0 ≤ a := by dsimp [a,sourceExclusionWidth]; positivity
  have hS : MeasurableSet ({z : Fin 6 × (ℝ × ℝ) | 1-a ≤ z.2.1} ∪ {z | z.2.2 ≤ a}) :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).union
    (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)
  change (sourceBiasedLaw j) ((fun ω : SourceBiasedSample => ω ⟨j+1+n,i⟩) ⁻¹'
    ({z | 1-a ≤ z.2.1} ∪ {z | z.2.2 ≤ a})) ≤ ENNReal.ofReal (20*a)
  rw [sourceBiasedCoordinate_measure _ _ _ hS]
  apply (measure_union_le _ _).trans
  apply (add_le_add (p.labelledCoupling_right_tail a) (p.labelledCoupling_left_tail a)).trans_eq
  rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) ha) (mul_nonneg (by norm_num) ha)]
  congr 1
  ring

theorem sourceFutureBoundary_no_bad (j : ℕ) (ω : SourceBiasedSample)
    (h : ω ∈ sourceFutureBoundaryEvent j) (n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) :
    (ω ⟨j+1+n,i⟩).2.1 < 1-sourceExclusionWidth j ⟨j+1+n,i⟩ ∧
      sourceExclusionWidth j ⟨j+1+n,i⟩ < (ω ⟨j+1+n,i⟩).2.2 := by
  have hn : ω ∉ sourceFutureBad j n i := by
    intro hb
    exact h (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨i,hb⟩⟩)
  exact ⟨lt_of_not_ge (fun hx => hn (Or.inl hx)),lt_of_not_ge (fun hy => hn (Or.inr hy))⟩

end
end FiniteFactor

end OAI
