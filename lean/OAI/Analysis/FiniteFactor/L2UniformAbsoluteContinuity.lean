import OAI.Analysis.FiniteFactor.TailEstimate
import Mathlib.MeasureTheory.Measure.WithDensityFinite

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Cauchy--Schwarz bounds the mass of any Borel set under an actual L2
density, in terms of the original reference measure of the set. -/
theorem withDensity_L2_set_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ)
    (hg : MemLp g 2 μ) (hg0 : ∀ x, 0 ≤ g x)
    (A : Set X) (hA : MeasurableSet A) (C : ℝ) (hC : (∫ x, g x ^ 2 ∂μ) ≤ C) :
    (μ.withDensity (fun x => ENNReal.ofReal (g x))) A ≤
      ENNReal.ofReal (Real.sqrt C * Real.sqrt ((μ A).toReal)) := by
  have hi : MemLp (A.indicator (fun _ : X => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have hcs := integral_mul_le_sqrt_squares hg hi
    (Eventually.of_forall hg0)
    (Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
  have hint : (∫ x, g x * A.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = ∫ x in A, g x ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hsquare : (∫ x, (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2 ∂μ) = (μ A).toReal := by
    have he : (fun x => (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2) =
        A.indicator (fun _ : X => (1 : ℝ)) := by
      funext x; by_cases hx : x ∈ A <;> simp [hx]
    rw [he, integral_indicator hA]
    simp [measureReal_def]
  rw [hint, hsquare] at hcs
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal
    (hg.integrable (by norm_num)).restrict (Eventually.of_forall hg0)]
  exact ENNReal.ofReal_le_ofReal (hcs.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)))

/-- Uniform L2 density bounds imply uniform absolute continuity, with no
measurable-selection premise for the densities. -/
theorem uniformAC_of_L2_densities {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ℕ → Measure X) (C : ℝ)
    (hν : ∀ n, ∃ g : X → ℝ, MemLp g 2 μ ∧ (∀ x, 0 ≤ g x) ∧
      ν n = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ (∫ x, g x^2 ∂μ) ≤ C)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → μ A < δ → ∀ n, ν n A ≤ ε := by
  let r : ℝ := (ε : ℝ) / (Real.sqrt C + 1)
  have hr : 0 < r := div_pos (by exact_mod_cast hε) (by positivity)
  refine ⟨ENNReal.ofReal (r^2), ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr), ?_⟩
  intro A hA hμ n
  obtain ⟨g,hg,hg0,he,hgC⟩ := hν n
  rw [he]
  apply (withDensity_L2_set_le μ g hg hg0 A hA C hgC).trans
  have hreal : (μ A).toReal ≤ r^2 := by
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hμ.le)
  have hs : Real.sqrt ((μ A).toReal) ≤ r := by
    exact (Real.sqrt_le_sqrt hreal).trans_eq (Real.sqrt_sq hr.le)
  have hmul : Real.sqrt C * r ≤ (ε : ℝ) := by
    have heq : r * (Real.sqrt C + 1) = (ε : ℝ) := div_mul_cancel₀ _ (by positivity)
    nlinarith [Real.sqrt_nonneg C]
  exact (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg C)).trans hmul)).trans_eq (by simp)

end
end FiniteFactor

end OAI
