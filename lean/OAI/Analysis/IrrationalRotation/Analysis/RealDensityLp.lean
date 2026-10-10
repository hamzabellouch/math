import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.DensityTransport

variable {X : Type*} [MeasurableSpace X]

lemma exists_Lp_density_of_memLp (μ ν : Measure X) {g : X → ℝ} {B : ℝ}
    (hg : MemLp g 2 μ) (hn : 0 ≤ᵐ[μ] g)
    (heq : ν = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (hB : 0 ≤ B) (hb : eLpNorm g 2 μ ≤ ENNReal.ofReal B) :
    ∃ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] (f : X → ℝ)) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ‖f‖ ≤ B := by
  refine ⟨hg.toLp g, ?_, ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp, hn] with x hx hnx
    simpa only [hx] using hnx
  · rw [heq]
    apply withDensity_congr_ae
    exact hg.coeFn_toLp.mono (fun x hx => congrArg ENNReal.ofReal hx.symm)
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal hB)

end Invariant233.DensityTransport

end OAI
