import OAI.NumberTheory.DukePrimeDegree.Dynamics.ReturnTowerLevels
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! # First return times have finite mass-weighted mean -/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal
namespace DukePrimeDegree

theorem firstReturnLevel_mass_sum_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    (∑' n : ℕ, (n+1:ℝ≥0∞)*μ (firstReturnLevel T S n)) ≤ μ univ := by
  have hEi (j : ℕ) : MeasurableEmbedding (T^[j]) := by
    induction j with
    | zero => exact MeasurableEmbedding.id
    | succ j ih =>
        rw [Function.iterate_succ]
        exact ih.comp hE
  have hm (p : Σ n : ℕ, Fin (n+1)) : MeasurableSet (firstReturnTower T S p) :=
    (hEi p.2.val).measurableSet_image.mpr
      (measurableSet_firstReturnLevel hT.measurable hS p.1)
  have hv (p : Σ n : ℕ, Fin (n+1)) :
      μ (firstReturnTower T S p)=μ (firstReturnLevel T S p.1) := by
    calc
      μ (firstReturnTower T S p) =
          (μ.map (T^[p.2.val])) (firstReturnTower T S p) := by
        rw [(hT.iterate p.2.val).map_eq]
      _ = μ ((T^[p.2.val]) ⁻¹' firstReturnTower T S p) :=
        Measure.map_apply (hT.measurable.iterate p.2.val) (hm p)
      _ = μ (firstReturnLevel T S p.1) :=
        congrArg μ ((hEi p.2.val).injective.preimage_image _)
  have hs : (∑' p : Σ n : ℕ, Fin (n+1), μ (firstReturnTower T S p)) =
      ∑' n : ℕ, (n+1:ℝ≥0∞)*μ (firstReturnLevel T S n) := by
    rw [ENNReal.tsum_sigma']
    simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  rw [←hs,←measure_iUnion (pairwise_disjoint_firstReturnTower T hE.injective S) hm]
  exact measure_mono (subset_univ _)

/-- This finite first moment is the return-time estimate used to keep the
refined countable partition's Shannon entropy finite. -/
theorem summable_firstReturnLevel_mass
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    Summable (fun n : ℕ => (n+1:ℝ)*μ.real (firstReturnLevel T S n)) := by
  have hb := firstReturnLevel_mass_sum_le μ hT hE hS
  have ht : (∑' n : ℕ, (n+1:ℝ≥0∞)*μ (firstReturnLevel T S n)) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ univ) hb
  have hs := ENNReal.summable_toReal ht
  have he (n : ℕ) : (n+1:ℝ≥0∞).toReal=(n+1:ℝ) := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast,ENNReal.toReal_one]
  apply hs.congr
  intro n
  rw [ENNReal.toReal_mul,he]
  rfl

end DukePrimeDegree

end

end OAI
