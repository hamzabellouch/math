import OAI.MathematicalPhysics.Boltzmann.Branching.TightApproximation
import OAI.MathematicalPhysics.Boltzmann.Branching.DensityCompactness

namespace OAI

/-! # Fixed outer-annulus majorants give tightness in all velocity variables -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem outer_unifTight_of_bound {f : ℕ → X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {g : X × Y → ℝ} (hg : Integrable g (μ.prod ν)) (hgn : ∀ z, 0 ≤ g z)
    {S : Set X} (hS : MeasurableSet S)
    (hle : ∀ n, ∀ᵐ p ∂μ.prod ν, p.1 ∉ S → f n p ≤ g p) :
    UnifTight (fun n => outerCutoff S (f n)) 1 (μ.prod ν) := by
  apply unifTight_of_integrable_majorant hg
    (fun n => ((hfm n).indicator (hS.compl.preimage measurable_fst)).aestronglyMeasurable)
  intro n
  filter_upwards [hle n] with p hp
  apply enorm_le_iff_norm_le.mpr
  have hn : 0 ≤ outerCutoff S (f n) p := indicator_nonneg (fun p _ => hf n p) p
  change ‖outerCutoff S (f n) p‖ ≤ ‖g p‖
  rw [Real.norm_of_nonneg hn,Real.norm_of_nonneg (hgn p)]
  by_cases hs : p.1 ∈ S
  · rw [outerCutoff,indicator_of_notMem (show p ∉ Prod.fst ⁻¹' Sᶜ from fun h => h hs)]
    exact hgn p
  · rw [outerCutoff,indicator_of_mem (show p ∈ Prod.fst ⁻¹' Sᶜ from hs)]
    exact hp hs

theorem outer_density_unifTight [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UnifTight (fun n => outerCutoff S (f n)) 1 (μ.prod (volume : Measure Velocity)) := by
  have hi : Integrable (fun p : X × Velocity => A*H q p.2) (μ.prod volume) :=
    ((integrable_H hq).const_mul A).comp_snd μ
  apply outer_unifTight_of_bound hfm hf hi (fun p => mul_nonneg hA (H_nonneg q p.2)) hS
  intro n
  have hHm : Measurable (fun p : X × Velocity => A*H q p.2) := by
    unfold H singularity
    fun_prop
  have hmP : MeasurableSet {p : X × Velocity | p.1 ∉ S → f n p ≤ A*H q p.2} := by
    convert (hS.preimage measurable_fst).union (measurableSet_le (hfm n) hHm) using 1
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_preimage,not_not,imp_iff_not_or]
  exact (Measure.ae_prod_iff_ae_ae hmP).mpr (hdom n)

theorem outer_pairs_unifTight [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UnifTight (fun n => outerCutoff S (pairDensity (f n))) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hi : Integrable (fun z : X × (Velocity × Velocity) => A^2*pairKernel q z.2)
      (μ.prod volume) := ((pairKernel_integrable hq).const_mul (A^2)).comp_snd μ
  apply outer_unifTight_of_bound (fun n => pairDensity_measurable (hfm n))
    (fun n => pairDensity_nonneg (hf n)) hi
    (fun z => mul_nonneg (sq_nonneg A) (pairKernel_nonneg q z.2)) hS
  intro n
  filter_upwards [pair_ae_bound (hfm n) hS A q (hdom n)] with z hz hs
  exact pairDensity_bound hA (hf n) z (hz hs).1 (hz hs).2

theorem outer_gainLoss_unifTight [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UnifTight (fun n => outerCutoff S (gainDensity (f n))) 1
      (μ.prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => outerCutoff S (lossDensity (f n))) 1
      (μ.prod (volume : Measure Velocity)) := by
  have hgn (z : X × Velocity) : 0 ≤ A*H q z.2 := mul_nonneg hA (H_nonneg q z.2)
  have hgm : Measurable (fun z : X × Velocity => A*H q z.2) := by
    unfold H singularity
    fun_prop
  have hi := gainLoss_integrable (μ := μ) hgm hgn (hot_pairDensity_integrable (μ := μ) hq A)
  have hb (n) := gainLoss_outer_bound hq hA (hfm n) (hf n) hS (hdom n)
  exact ⟨outer_unifTight_of_bound (fun n => gainDensity_measurable (hfm n))
      (fun n => gainDensity_nonneg (hf n)) hi.1 (gainDensity_nonneg hgn) hS
      (fun n => (hb n).mono (fun p hp hs => (hp hs).1)),
    outer_unifTight_of_bound (fun n => lossDensity_measurable (hfm n))
      (fun n => lossDensity_nonneg (hf n)) hi.2 (lossDensity_nonneg hgn) hS
      (fun n => (hb n).mono (fun p hp hs => (hp hs).2))⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
