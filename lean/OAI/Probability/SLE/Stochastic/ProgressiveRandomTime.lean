import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace OAI

/-! Measurable evaluation of a progressive process at an arbitrary finite
random time. The target needs only a measurable-space structure. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace MeasureTheory.IsProgressive
open scoped _root_.MeasureTheory _root_.MeasureTheory.IsProgressive

theorem random_time_measurable
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {ℱ : _root_.MeasureTheory.Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → X}
    (hN : _root_.MeasureTheory.IsProgressive ℱ N) (T : Ω → ℝ≥0) (hT : Measurable T) :
    Measurable (fun ω => N (T ω) ω) := by
  let f (n : ℕ) (ω : Ω) := N (min (T ω) (n:ℝ≥0)) ω
  have hf (n : ℕ) : Measurable (f n) := by
    have ht : Measurable (fun ω => (⟨min (T ω) (n:ℝ≥0),Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic (n:ℝ≥0))) :=
      (hT.min measurable_const).subtype_mk
    have hω : @Measurable Ω Ω mΩ (ℱ (n:ℝ≥0)) id := by
      intro A hA
      exact ℱ.le (n:ℝ≥0) A hA
    have hp : @Measurable Ω (Iic (n:ℝ≥0) × Ω) mΩ
        (Subtype.instMeasurableSpace.prod (ℱ (n:ℝ≥0)))
        (fun ω => (⟨min (T ω) (n:ℝ≥0),Set.mem_Iic.mpr (min_le_right _ _)⟩,ω)) := ht.prodMk hω
    exact (hN (n:ℝ≥0)).comp hp
  intro A hA
  have he : (fun ω => N (T ω) ω) ⁻¹' A =
      ⋃ n : ℕ, {ω | T ω ≤ (n:ℝ≥0)} ∩ (f n) ⁻¹' A := by
    ext ω
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hω
      obtain ⟨n,hn⟩ := exists_nat_ge (T ω : ℝ)
      have htn : T ω ≤ (n:ℝ≥0) := by exact_mod_cast hn
      exact ⟨n,htn,by simpa only [f,min_eq_left htn] using hω⟩
    · rintro ⟨n,hn,hω⟩
      simpa only [f,min_eq_left hn] using hω
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    (measurableSet_le hT measurable_const).inter (hf n hA))

theorem extended_random_time_measurable
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {ℱ : _root_.MeasureTheory.Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → X}
    (hN : _root_.MeasureTheory.IsProgressive ℱ N) (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun ω => N (S ω).toNNReal ω) :=
  _root_.OAI.MeasureTheory.IsProgressive.random_time_measurable hN (fun ω => (S ω).toNNReal) (ENNReal.measurable_toNNReal.comp hS)

end MeasureTheory.IsProgressive

end

end OAI
