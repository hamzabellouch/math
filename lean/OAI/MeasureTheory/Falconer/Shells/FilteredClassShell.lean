import OAI.MeasureTheory.Falconer.Shells.FiniteWeightedShell
import OAI.MeasureTheory.Falconer.Shells.TwoSidedShell

namespace OAI

/-! # Class mixtures cost only the square of the product-filter count -/

namespace Falconer
open Set MeasureTheory
open scoped NNReal

theorem positive_shell_finite_sum {ι : Type*} (F : Finset ι)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ) {E : ℝ}
    (hτ : ∀ i ∈ F,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun (τ i) r‖^2) ≤ E) :
    (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
      ‖charFun (∑ i ∈ F, τ i) r‖^2) ≤ (F.card:ℝ)^2*E := by
  have he (r : ℝ) : charFun (∑ i ∈ F, τ i) r = ∑ i ∈ F, charFun (τ i) r := by
    simpa using PlanarFalconer.charFun_weighted_sum F (fun _ => (1:ℝ≥0)) τ r
  simp_rw [he]
  have hi (i : ι) : IntegrableOn (fun r => ‖charFun (τ i) r‖^2)
      (Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1))) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hb := PlanarFalconer.finite_weighted_shell_square F
    (volume.restrict (Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1))))
    (fun i r => charFun (τ i) r) (fun _ => (1:ℝ))
    (fun _ _ => zero_le_one) (fun i _ => hi i)
    (fun _ _ => continuous_charFun.aestronglyMeasurable)
    (fun i hi => by simpa using hτ i hi)
  simpa using hb

theorem shellEnergy_filter_mixture {ι : Type*} (F : Finset ι)
    (c : ι → ℝ≥0) (n N : ℕ) (τ : ι → Fin n → Measure ℝ)
    [∀ i j, IsFiniteMeasure (τ i j)] (hc : (∑ i ∈ F, (c i:ℝ)) ≤ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (hτ : ∀ i ∈ F, ∀ j,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun (τ i j) r‖^2) ≤ E) :
    PlanarFalconer.shellEnergy (∑ i ∈ F, c i • ∑ j, τ i j) N ≤ 2*(n:ℝ)^2*E := by
  apply PlanarFalconer.shellEnergy_weighted_sum_uniform F c (fun i => ∑ j, τ i j) N hc
    (by positivity)
  intro i hi
  rw [PlanarFalconer.shellEnergy_eq_twice_positive]
  have hh := positive_shell_finite_sum Finset.univ (τ i) N (fun j _ => hτ i hi j)
  simpa only [Finset.card_univ,Fintype.card_fin,mul_assoc] using
    mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)

end Falconer

end OAI
