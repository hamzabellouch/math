import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds
import OAI.Analysis.RieszRectifiability.Limits.WeakCellMass

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_continuitySet_mass_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d))
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure (Ambient d)).real s) atTop
      (𝓝 ((ν : Measure (Ambient d)).real s)) := by
  by_cases hν : ν = 0
  · subst ν
    have ht : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop (𝓝 0) := by
      simpa using! NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    simpa using! squeeze_zero (fun _ => measureReal_nonneg)
      (fun j => measureReal_mono (μ := (μ j : Measure (Ambient d))) (subset_univ s)) ht
  · exact finiteMeasure_cell_mass_tendsto μ ν hweak hν s hboundary

def weightedFiniteMeasure {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) : FiniteMeasure (Ambient d) :=
  ⟨(μ : Measure (Ambient d)).withDensity (fun x => (f x : ℝ≥0∞)),
    isFiniteMeasure_withDensity (f.lintegral_lt_top_of_nnreal (μ : Measure (Ambient d))).ne⟩

theorem weightedFiniteMeasure_integral {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(weightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂(μ : Measure (Ambient d)) := by
  exact integral_withDensity_eq_integral_smul (μ := (μ : Measure (Ambient d)))
    f.continuous.measurable g

theorem weightedFiniteMeasure_real_set {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (s : Set (Ambient d)) (hs : MeasurableSet s) :
    (weightedFiniteMeasure μ f : Measure (Ambient d)).real s =
      ∫ x in s, (f x : ℝ) ∂(μ : Measure (Ambient d)) := by
  change ((μ : Measure (Ambient d)).withDensity (fun x => (f x : ℝ≥0∞))).real s = _
  rw [Measure.real, withDensity_apply _ hs]
  exact f.toReal_lintegral_coe_eq_integral ((μ : Measure (Ambient d)).restrict s)

theorem weightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => weightedFiniteMeasure (μ j) f) atTop (𝓝 (weightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [weightedFiniteMeasure_integral]
  let f₀ : Ambient d →ᵇ ℝ := BoundedContinuousFunction.comp ((↑) : ℝ≥0 → ℝ)
    NNReal.isometry_coe.lipschitzWith f
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f₀ * g)

theorem weak_setIntegral_nnreal_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => ∫ x in s, (f x : ℝ) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, (f x : ℝ) ∂(ν : Measure (Ambient d)))) := by
  have hb : (weightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := finiteMeasure_continuitySet_mass_tendsto (fun j => weightedFiniteMeasure (μ j) f)
    (weightedFiniteMeasure ν f) (weightedFiniteMeasure_tendsto μ ν hweak f) s hb
  simpa only [weightedFiniteMeasure_real_set _ f s hs] using! h

theorem weak_setIntegral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ x in s, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, f x ∂(ν : Measure (Ambient d)))) := by
  have hp := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary f.nnrealPart
  have hn := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary (-f).nnrealPart
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub] using! hp.sub hn

def restrictedFiniteMeasure {d : ℕ} (μ : FiniteMeasure (Ambient d)) (s : Set (Ambient d)) :
    FiniteMeasure (Ambient d) := ⟨(μ : Measure (Ambient d)).restrict s, inferInstance⟩

theorem restrictedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => restrictedFiniteMeasure (μ j) s) atTop (𝓝 (restrictedFiniteMeasure ν s)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact fun f => weak_setIntegral_tendsto μ ν hweak s hs hboundary f

end

end RieszRectifiability

end OAI
