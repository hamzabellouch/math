import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaOrder

namespace OAI

/-! # Entropy along increasing conditioning sigma algebras

The martingale limit applies also when the conditioning includes an
arbitrary transverse coordinate in addition to finite future names.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma finiteShannon_norm_le_card_of_unit_bounds {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, p a ∈ Icc 0 1) :
    ‖finiteShannon p‖ ≤ Fintype.card α := by
  unfold finiteShannon
  calc
    ‖∑ a, Real.negMulLog (p a)‖ ≤ ∑ a, ‖Real.negMulLog (p a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : α, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hp a).1 (hp a).2)]
      have H := Real.negMulLog_le_one_sub_self (hp a).1
      linarith [(hp a).1]
    _ = _ := by simp

theorem conditionalSigmaEntropy_tendsto_iSup {Y α : Type*}
    [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (m : ℕ → MeasurableSpace Y) (hm : Monotone m) (hle : ∀ n, m n ≤ mY) :
    Tendsto (fun n => conditionalSigmaEntropy (mY := mY) μ P (m n)) atTop
      (𝓝 (conditionalSigmaEntropy (mY := mY) μ P (⨆ n, m n))) := by
  let ℱ : Filtration ℕ mY := ⟨m,hm,hle⟩
  let g (a : α) : Y → ℝ := {z | P z=a}.indicator (fun _ => 1)
  let F : ℕ → Y → ℝ := fun n y => finiteShannon (fun a => (μ[g a | m n]) y)
  let G : Y → ℝ := fun y => finiteShannon (fun a => (μ[g a | ⨆ n, m n]) y)
  have hFi n : Integrable (F n) μ := by
    change Integrable (fun y => ∑ a, Real.negMulLog ((μ[g a | m n]) y)) μ
    apply integrable_finsetSum
    intro a _
    exact integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {z | P z=a} (m n))
  have hbound n : ∀ᵐ y ∂μ, ‖F n y‖ ≤ (Fintype.card α:ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun a =>
      conditionalProbability_unit_bounds (mY := mY) μ {z | P z=a} (m n))] with y hy
    exact finiteShannon_norm_le_card_of_unit_bounds _ hy
  have hcoord (a : α) : ∀ᵐ y ∂μ, Tendsto (fun n => (μ[g a | m n]) y) atTop
      (𝓝 ((μ[g a | ⨆ n, m n]) y)) := by
    exact MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (g a)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 (G y)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with y hy
    have H := continuous_finiteShannon.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hy)
    simpa only [F,G,Function.comp_def] using H
  have H := tendsto_integral_of_dominated_convergence
    (fun _ : Y => (Fintype.card α:ℝ)) (fun n => (hFi n).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  simpa only [conditionalSigmaEntropy,F,G,g] using H

end DukePrimeDegree

end

end OAI
