import OAI.MeasureTheory.Falconer.Shells.Shells
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem norm_weighted_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) (z : ι → ℂ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ ∑ i ∈ s, (c i : ℝ) * ‖z i‖^2 := by
  have hn : ‖∑ i ∈ s, (c i : ℝ) • z i‖ ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      norm_sum_le s (fun i => (c i : ℝ) • z i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => (c i : ℝ)) (g := fun i => (c i : ℝ)*‖z i‖^2)
    (r := fun i => (c i : ℝ)*‖z i‖)
    (fun _ _ => NNReal.coe_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => by nlinarith)
  have hg : 0 ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖^2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsq : ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ (∑ i ∈ s, (c i : ℝ)*‖z i‖)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (hs.trans (by nlinarith))

theorem charFun_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (r : ℝ) :
    charFun (∑ i ∈ s, c i • τ i) r = ∑ i ∈ s, (c i : ℝ) • charFun (τ i) r := by
  simp only [charFun_eq_integral_innerProbChar]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_smul_nnreal_measure _ _
  · intro i hi
    exact (BoundedContinuousFunction.innerProbChar r).integrable _

theorem shellEnergy_weighted_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ ∑ i ∈ s, (c i : ℝ)*shellEnergy (τ i) N := by
  have hi : IntegrableOn (fun r => ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2) (dyadicShell N) volume :=
    integrable_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)
  have hpoint (r : ℝ) : ‖charFun (∑ i ∈ s, c i • τ i) r‖^2 ≤
      ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 := by
    rw [charFun_weighted_sum]
    exact norm_weighted_sum_sq_le s c _ hc
  unfold shellEnergy
  calc
    _ ≤ ∫ r in dyadicShell N, ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 :=
      integral_mono (shell_energy_integrable _ N) hi hpoint
    _ = _ := by
      rw [integral_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)]
      simp_rw [integral_const_mul]

theorem shellEnergy_weighted_sum_uniform {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hτ : ∀ i ∈ s, shellEnergy (τ i) N ≤ C) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ C := by
  apply (shellEnergy_weighted_sum_le s c τ N hc).trans
  calc
    _ ≤ ∑ i ∈ s, (c i : ℝ)*C := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hτ i hi) (NNReal.coe_nonneg _))
    _ = (∑ i ∈ s, (c i : ℝ))*C := (Finset.sum_mul ..).symm
    _ ≤ C := by nlinarith

end PlanarFalconer

end OAI
