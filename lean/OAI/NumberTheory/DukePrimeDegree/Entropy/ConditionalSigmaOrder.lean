import OAI.NumberTheory.PrimePackets.ConditionalSigmaEntropy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

namespace OAI

/-! # Conditioning on more measurable information decreases entropy

Conditional Jensen and the tower property apply directly to the actual
conditional expectations defining finite-observation entropy.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma integrable_negMulLog_of_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ y ∂μ, f y ∈ Icc 0 1) :
    Integrable (fun y => Real.negMulLog (f y)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hf)
  filter_upwards [hb] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg hy.1 hy.2)]
  have H := Real.negMulLog_le_one_sub_self hy.1
  linarith [hy.1]

lemma conditionalProbability_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) (S : Set Y) (m : MeasurableSpace Y) :
    ∀ᵐ y ∂μ, (μ[S.indicator (fun _ => (1:ℝ)) | m]) y ∈ Icc 0 1 := by
  have hn : 0 ≤ᵐ[μ] S.indicator (fun _ => (1:ℝ)) := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  have hu : ∀ᵐ y ∂μ, S.indicator (fun _ => (1:ℝ)) y ≤ 1 := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  filter_upwards [condExp_nonneg (m := m) hn,
    condExp_le_nonneg_const (m := m) (show (0:ℝ)≤1 by norm_num) hu] with y hy hz
  exact ⟨hy,hz⟩

theorem conditionalSigmaEntropy_antitone {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    {m n : MeasurableSpace Y} (hmn : m ≤ n) (hn : n ≤ mY) :
    conditionalSigmaEntropy (mY := mY) μ P n ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  have hm := hmn.trans hn
  let g (a : α) : Y → ℝ := {y | P y=a}.indicator (fun _ => 1)
  have hg a : Integrable (g a) μ := (integrable_const (1:ℝ)).indicator (hP a)
  have hi (s : MeasurableSpace Y) (hs : s ≤ mY) (a : α) :
      Integrable (fun y => Real.negMulLog ((μ[g a | s]) y)) μ :=
    integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono hs).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} s)
  unfold conditionalSigmaEntropy finiteShannon
  rw [integral_finsetSum _ (fun a _ => hi n hn a),
    integral_finsetSum _ (fun a _ => hi m hm a)]
  apply Finset.sum_le_sum
  intro a _
  have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := μ) (f := μ[g a | n]) hm
    (Real.continuous_negMulLog.upperSemicontinuous.upperSemicontinuousOn _)
    ((conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} n).mono fun _ h => h.1)
    isClosed_Ici integrable_condExp (hi n hn a)
  have hTower := condExp_condExp_of_le (μ := μ) (f := g a) hmn hn
  have hle : (μ[(fun y => Real.negMulLog ((μ[g a | n]) y)) | m]) ≤ᵐ[μ]
      (fun y => Real.negMulLog ((μ[g a | m]) y)) := by
    filter_upwards [hJ,hTower] with y hy ht
    simpa only [Function.comp_def,ht] using hy
  calc
    _ = ∫ y, (μ[(fun z => Real.negMulLog ((μ[g a | n]) z)) | m]) y ∂μ :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp (hi m hm a) hle

end DukePrimeDegree

end

end OAI
