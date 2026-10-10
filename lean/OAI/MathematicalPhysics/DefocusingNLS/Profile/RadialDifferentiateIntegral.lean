import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Differentiating the regular radial integral along a one-sided interval. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_hasDerivWithinAt_integral (F : ℝ → ℝ → ℂ) (D : ℝ → ℂ)
    (s : Set ℝ) (x₀ C : ℝ)
    (hF : ∀ x ∈ s, IntegrableOn (F x) (Icc (0 : ℝ) 1))
    (hF₀ : IntegrableOn (F x₀) (Icc (0 : ℝ) 1))
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun x => F x t) (D t) s x₀)
    (hB : ∀ᶠ x in nhdsWithin x₀ (s \ {x₀}),
      ∀ t ∈ Icc (0 : ℝ) 1, ‖slope (fun y => F y t) x₀ x‖ ≤ C) :
    HasDerivWithinAt (fun x => ∫ t in Icc (0 : ℝ) 1, F x t)
      (∫ t in Icc (0 : ℝ) 1, D t) s x₀ := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hm : ∀ᶠ x in nhdsWithin x₀ (s \ {x₀}),
      AEStronglyMeasurable (fun t => slope (fun y => F y t) x₀ x) μ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((hF x hx.1).aestronglyMeasurable.sub hF₀.aestronglyMeasurable).const_smul _
  have hb : ∀ᶠ x in nhdsWithin x₀ (s \ {x₀}),
      ∀ᵐ t ∂μ, ‖slope (fun y => F y t) x₀ x‖ ≤ C := by
    filter_upwards [hB] with x hx
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hx)
  have hd : ∀ᵐ t ∂μ, Tendsto (fun x => slope (fun y => F y t) x₀ x)
      (nhdsWithin x₀ (s \ {x₀})) (nhds (D t)) := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact Eventually.of_forall (fun t ht => hasDerivWithinAt_iff_tendsto_slope.mp (hD t ht))
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (fun _ => C) hm hb (integrableOn_const (by simp)) hd
  rw [hasDerivWithinAt_iff_tendsto_slope]
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [slope_def_module]
  rw [integral_smul,integral_sub (hF x hx.1) hF₀]

end DefocusingNLS

end OAI
