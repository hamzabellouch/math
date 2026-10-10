import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

noncomputable def intervalLaw (a L : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / L) • volume.restrict (Ioc a (a + L))

noncomputable def phaseLaw (a L : ℝ) : Measure UnitAddCircle :=
  (intervalLaw a L).map (fun x : ℝ => (x : UnitAddCircle))

noncomputable def phaseDensity (a L : ℝ) (x : UnitAddCircle) : ℝ :=
  ((phaseLaw a L).rnDeriv volume x).toReal

noncomputable def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco 1 0 x : ℝ)

noncomputable def lambdaLaw (N₀ : ℝ) : Measure ℝ :=
  ENNReal.ofReal N₀ • volume.restrict (Icc (1 / N₀) (2 / N₀))

noncomputable def fractionLaw (N₀ n : ℝ) : Measure ℝ :=
  (lambdaLaw N₀).map (fun x => Int.fract (n * x))

noncomputable def fractionDensity (N₀ n x : ℝ) : ℝ :=
  ((fractionLaw N₀ n).rnDeriv (volume.restrict (Ico 0 1)) x).toReal

end Invariant233.UniformIntervalPhase

end OAI
