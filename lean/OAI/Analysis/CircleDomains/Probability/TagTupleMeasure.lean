import OAI.Analysis.CircleDomains.Selection.TagCodeSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def LevelTuple := Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)

instance : TopologicalSpace LevelTuple :=
  inferInstanceAs (TopologicalSpace (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)))
instance : MeasurableSpace LevelTuple := borel LevelTuple
instance : BorelSpace LevelTuple := ⟨rfl⟩
instance : SecondCountableTopology LevelTuple :=
  inferInstanceAs (SecondCountableTopology
    (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)))
instance : IsCompletelyMetrizableSpace LevelTuple := by
  change IsCompletelyMetrizableSpace
    (Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle))
  infer_instance
instance : PolishSpace LevelTuple := by infer_instance

def tagDataTuple (q : TagData) : LevelTuple := ⟨q.1, q.2.1, q.2.2.1⟩

theorem continuous_tagDataTuple : Continuous tagDataTuple := by
  apply continuous_sigma
  intro n
  exact continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd.fst)

def slotTupleMeasure : TagSlot → Measure LevelTuple :=
  Sum.elim (fun _ => 0) (fun q => Measure.dirac (tagDataTuple q))

def activeTagSlot (q : TagData) : TagSlot := Sum.inr q

theorem measurable_slotTupleMeasure : Measurable slotTupleMeasure := by
  classical
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let S : Set TagSlot := activeTagSlot '' (tagDataTuple ⁻¹' A)
  have hi : IsOpenEmbedding activeTagSlot := IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  have himg : MeasurableSet S := hme.measurableSet_image.mpr
    (continuous_tagDataTuple.measurable hA)
  have heq : (fun s => slotTupleMeasure s A) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext s
    cases s with
    | inl u =>
      have hnot : (Sum.inl u : TagSlot) ∉ S := by
        rintro ⟨q, _, he⟩
        cases he
      change 0 = if (Sum.inl u : TagSlot) ∈ S then 1 else 0
      rw [ite_eq_right hnot]
    | inr q =>
      have hmem : (Sum.inr q : TagSlot) ∈ S ↔ tagDataTuple q ∈ A := by
        constructor
        · rintro ⟨p, hp, hpq⟩
          cases Sum.inr.inj hpq
          exact hp
        · intro hq
          exact ⟨q, hq, rfl⟩
      change (Measure.dirac (tagDataTuple q)) A = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [Measure.dirac_apply' _ hA]
      change (if tagDataTuple q ∈ A then 1 else 0) = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [hmem]
  rw [heq]
  exact measurable_const.indicator himg

theorem slotTupleMeasure_univ_le (s : TagSlot) : slotTupleMeasure s univ ≤ 1 := by
  cases s with
  | inl u => simp [slotTupleMeasure]
  | inr q => simp [slotTupleMeasure]

def slotWeight (k : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ k

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem tsum_slotWeight : ∑' k, slotWeight k = 2 := ENNReal.tsum_geometric_two

def weightedTupleMeasure (θ : ℕ → TagSlot) : Measure LevelTuple :=
  Measure.sum (fun k => slotWeight k • slotTupleMeasure (θ k))

theorem weightedTupleMeasure_apply (θ : ℕ → TagSlot) {s : Set LevelTuple}
    (hs : MeasurableSet s) :
    weightedTupleMeasure θ s = ∑' k, slotWeight k * slotTupleMeasure (θ k) s := by
  simp only [weightedTupleMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

theorem weightedTupleMeasure_mass_le (θ : ℕ → TagSlot) : weightedTupleMeasure θ univ ≤ 2 := by
  rw [weightedTupleMeasure_apply θ MeasurableSet.univ, ← tsum_slotWeight]
  exact ENNReal.tsum_le_tsum fun k =>
    mul_le_of_le_one_right (bot_le) (slotTupleMeasure_univ_le (θ k))

instance (θ : ℕ → TagSlot) : IsFiniteMeasure (weightedTupleMeasure θ) :=
  ⟨lt_of_le_of_lt (weightedTupleMeasure_mass_le θ) (by norm_num)⟩

theorem measurable_weightedTupleMeasure : Measurable weightedTupleMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [weightedTupleMeasure_apply _ hs]
  apply Measurable.tsum
  intro k
  exact measurable_const.mul ((Measure.measurable_coe hs).comp
    (measurable_slotTupleMeasure.comp (measurable_pi_apply k)))

theorem weightedTupleMeasure_slot_le (θ : ℕ → TagSlot) (k : ℕ) :
    slotWeight k • slotTupleMeasure (θ k) ≤ weightedTupleMeasure θ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedTupleMeasure_apply θ hs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.le_tsum (f := fun j => slotWeight j * slotTupleMeasure (θ j) s) k

end CircleDomainRigidity

end

end OAI
