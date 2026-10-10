import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallReturnEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.FirstReturnPartition

namespace OAI

/-! # Uniformly small entropy for return partitions of small sections -/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal
namespace DukePrimeDegree

lemma firstReturnLevel_real_mass_sum_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) {S : Set Y} (hS : MeasurableSet S) :
    (∑' n, μ.real (firstReturnLevel T S n)) ≤ μ.real S := by
  have hd : Pairwise (Disjoint on firstReturnLevel T S) := by
    intro i j hij
    exact disjoint_left.mpr (fun _ hi hj => hij (firstReturnLevel_unique T S hi hj))
  have H : (∑' n, μ (firstReturnLevel T S n)) ≤ μ S := by
    rw [←measure_iUnion hd (fun n => measurableSet_firstReturnLevel hT hS n)]
    exact measure_mono (iUnion_subset fun _ _ hx => hx.1)
  have H' := ENNReal.toReal_mono (measure_ne_top μ S) H
  rwa [ENNReal.tsum_toReal_eq (fun _ => measure_ne_top μ _)] at H'

lemma firstReturnLevel_real_mean_le_one
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    (∑' n : ℕ, (n+1:ℝ)*μ.real (firstReturnLevel T S n)) ≤ 1 := by
  have H := ENNReal.toReal_mono (measure_ne_top μ univ)
    (firstReturnLevel_mass_sum_le μ hT hE hS)
  rw [ENNReal.tsum_toReal_eq (fun n => by finiteness),measure_univ,ENNReal.toReal_one] at H
  have he (n : ℕ) :
      ((n+1:ℝ≥0∞)*μ (firstReturnLevel T S n)).toReal =
        (n+1:ℝ)*μ.real (firstReturnLevel T S n) := by
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast,ENNReal.toReal_one,Measure.real]
  simpa only [he] using H

lemma firstReturnPartitionCode_zero_mass
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {S : Set Y} (hS : MeasurableSet S) :
    μ.real {x | firstReturnPartitionCode T S x=0}=1-μ.real S := by
  have he : {x | firstReturnPartitionCode T S x=0} =
      (⋃ n, firstReturnLevel T S n)ᶜ := by
    ext x
    exact firstReturnPartitionCode_eq_iff T S x 0
  have hu : (⋃ n, firstReturnLevel T S n) =ᵐ[μ] S := by
    filter_upwards [ae_section_mem_firstReturnLevel μ hT hS] with x hx
    apply propext
    constructor
    · intro h
      obtain ⟨n,hn⟩ := mem_iUnion.mp h
      exact hn.1
    · intro h
      exact mem_iUnion.mpr (hx h)
  rw [he,measureReal_compl (MeasurableSet.iUnion fun n =>
    measurableSet_firstReturnLevel hT.measurable hS n)]
  have hm : μ.real (⋃ n, firstReturnLevel T S n)=μ.real S :=
    congrArg ENNReal.toReal (measure_congr hu)
  rw [hm]
  simp

lemma firstReturnPartitionCode_entropy_eq
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    (∑' n, Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=n})) =
      Real.negMulLog (1-μ.real S)+
        ∑' n, Real.negMulLog (μ.real (firstReturnLevel T S n)) := by
  have he (n : ℕ) : {x | firstReturnPartitionCode T S x=n+1}=
      firstReturnLevel T S n := by
    ext x
    exact firstReturnPartitionCode_eq_iff T S x (n+1)
  have hs : Summable (fun n => Real.negMulLog
      (μ.real {x | firstReturnPartitionCode T S x=n+1})) := by
    simpa only [he] using firstReturnPartition_information_summable μ hT hE hS
  have hz : Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=0}) =
      Real.negMulLog (1-μ.real S) :=
    congrArg Real.negMulLog (firstReturnPartitionCode_zero_mass μ hT hS)
  have ht : (∑' n, Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=n+1})) =
      ∑' n, Real.negMulLog (μ.real (firstReturnLevel T S n)) :=
    tsum_congr (fun n => congrArg (fun A => Real.negMulLog (μ.real A)) (he n))
  exact (tsum_eq_zero_add' (f := fun n => Real.negMulLog
    (μ.real {x | firstReturnPartitionCode T S x=n})) hs).trans (congrArg₂ (fun a b : ℝ => a+b) hz ht)

/-- The entropy threshold is uniform in the measure-preserving map and
section. In particular it may be chosen before the transverse return box. -/
theorem exists_small_section_return_entropy
    {Y : Type*} [MeasurableSpace Y] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure Y) [IsProbabilityMeasure μ]
      {T : Y → Y} (_hT : MeasurePreserving T μ μ) (_hE : MeasurableEmbedding T)
      {S : Set Y} (_hS : MeasurableSet S), μ.real S ≤ δ →
        (∑' n, Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=n})) < ε := by
  obtain ⟨δ,hδ,hbound⟩ := exists_small_mass_return_information_bound hε
  refine ⟨δ,hδ,?_⟩
  intro μ _ T hT hE S hS hsmall
  rw [firstReturnPartitionCode_entropy_eq μ hT hE hS]
  exact hbound (fun n => μ.real (firstReturnLevel T S n))
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (summable_firstReturnLevel_mass μ hT hE hS)
    (firstReturnLevel_real_mean_le_one μ hT hE hS)
    (μ.real S) measureReal_nonneg measureReal_le_one hsmall
    (firstReturnLevel_real_mass_sum_le μ hT.measurable hS)

end DukePrimeDegree

end

end OAI
