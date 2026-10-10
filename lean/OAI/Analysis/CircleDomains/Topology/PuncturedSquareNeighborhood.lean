import OAI.Analysis.CircleDomains.Probability.CountableLawRestriction
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! Finite square mass admits a small punctured neighborhood of any point.
This controls the entire hit vector, including any later countable restriction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem punctured_square_norm_subtype_le {X : Type*} (m : X → ℝ≥0∞)
    (D U B : Set X) (p : X) :
    countingSquareNorm (fun x : ↥(D ∩ (U ∩ B)) => if x.val ≠ p then m x.val else 0) ≤
      countingSquareNorm (fun x : B => if x.val ∈ U ∧ x.val ≠ p then m x.val else 0) := by
  let f : ↥(D ∩ (U ∩ B)) → B := fun x => ⟨x.val, x.property.2.2⟩
  have hf : Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : B => z.val) h)
  have he : (fun x : ↥(D ∩ (U ∩ B)) => if x.val ≠ p then m x.val else 0) =
      (fun x : B => if x.val ∈ U ∧ x.val ≠ p then m x.val else 0) ∘ f := by
    funext x
    simp only [Function.comp_def, f, x.property.2.1, true_and]
  rw [he]
  exact countingSquareNorm_comp_injective _ f hf

theorem exists_open_punctured_square_norm {X A : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (x : A → X) (m : A → ℝ≥0∞) (hm : (∑' a, m a ^ 2) < ∞)
    (p : X) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ O : Set X, IsOpen O ∧ p ∈ O ∧
      countingSquareNorm (fun a => if x a ∈ O ∧ x a ≠ p then m a else 0) < δ := by
  let w : A → ℝ≥0∞ := fun a => if x a ≠ p then m a ^ 2 else 0
  let ν : Measure X := Measure.sum fun a => w a • Measure.dirac (x a)
  have hfin : ν univ < ∞ := by
    dsimp only [ν]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      mem_univ, indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
    exact (ENNReal.tsum_le_tsum (fun a => by dsimp only [w]; split_ifs <;> simp)).trans_lt hm
  let : IsFiniteMeasure ν := ⟨hfin⟩
  have hzero : ν {p} = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ (measurableSet_singleton p)]
    have hz (a : A) : (w a • Measure.dirac (x a)) {p} = 0 := by
      by_cases h : x a = p <;> simp [w, h]
    simp only [hz, tsum_zero]
  obtain ⟨O, hpO, hO, hmass⟩ := ({p} : Set X).exists_isOpen_lt_of_lt (μ := ν)
    (δ ^ 2) (hzero ▸ ENNReal.pow_pos hδ 2)
  have he : ν O = ∑' a, (if x a ∈ O ∧ x a ≠ p then m a else 0) ^ 2 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ hO.measurableSet]
    apply tsum_congr
    intro a
    by_cases ho : x a ∈ O <;> by_cases hp : x a = p <;> simp [w, ho, hp]
  refine ⟨O, hO, hpO (mem_singleton p), ?_⟩
  have hroot := ENNReal.rpow_lt_rpow hmass (by norm_num : (0 : ℝ) < 1 / 2)
  rw [he] at hroot
  have hpow : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [countingSquareNorm, Function.comp_def, hpow] using hroot

end CircleDomainRigidity

end

end OAI
