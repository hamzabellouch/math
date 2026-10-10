import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MeanSquareContinuity

def discrepancy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) : ℝ :=
  ∫ ω, (u s ω - u t ω) ^ 2 ∂P

@[simp] theorem discrepancy_self {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    discrepancy P u t t = 0 := by simp [discrepancy]

theorem discrepancy_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) :
    0 ≤ discrepancy P u s t := integral_nonneg (fun _ => sq_nonneg _)

theorem continuous_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => discrepancy P u p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => (2 * C) ^ 2)
  · intro p
    exact ((hm p.1).sub (hm p.2)).pow 2
  · intro p
    filter_upwards [hb] with ω hω
    have hn : |u p.1 ω - u p.2 ω| ≤ 2 * C :=
      (abs_sub _ _).trans (by linarith [hω p.1, hω p.2])
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hC)).mpr hn
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact ((hω.comp continuous_fst).sub (hω.comp continuous_snd)).pow 2

theorem uniform_discrepancy_small {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ≥0) T, ∀ t ∈ Icc (0 : ℝ≥0) T,
      dist s t < δ → discrepancy P u s t < ε := by
  have hcompact : IsCompact ((Icc (0 : ℝ≥0) T) ×ˢ (Icc (0 : ℝ≥0) T)) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC := hcompact.uniformContinuousOn_of_continuous
    (continuous_discrepancy hm hc hC hb).continuousOn
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  have hh := hsmall (s, t) ⟨hs, ht⟩ (t, t) ⟨ht, ht⟩
    (by simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hst)
  simpa only [discrepancy_self, Real.dist_eq, sub_zero,
    abs_of_nonneg (discrepancy_nonneg P u s t)] using hh

theorem uniform_integral_sq_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (t : ℝ) - (s : ℝ) ≤ δ → (∫ ω, (u s ω - u t ω) ^ 2 ∂P) ≤ ε := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_discrepancy_small hm hc hC hb T hε
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro s t hst ht hd
  apply (hsmall s ⟨bot_le, hst.trans ht⟩ t ⟨bot_le, ht⟩ ?_).le
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst))]
  linarith

end Problem367.MeanSquareContinuity

end

end OAI
