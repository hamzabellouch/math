import OAI.MeasureTheory.Falconer.Fourier.ActualDistanceLowBand
import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyMaximum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def prefixLowDepths (d : PositiveDistanceData) : Finset ℕ :=
  (Finset.Ioc d.a d.t).filter fun v => (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N

noncomputable def prefixLowMaximum (d : PositiveDistanceData) : ℝ :=
  finiteEnergyMaximum d.prefixLowDepths
    (fun v => ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence)

theorem prefixLowMaximum_nonneg (d : PositiveDistanceData) : 0 ≤ d.prefixLowMaximum :=
  finiteEnergyMaximum_nonneg _ _

theorem prefixLowMaximum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    {v : ℕ} (hv : v ∈ Finset.Ioc d.a d.t) (hvl : (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N) :
    ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence ≠ ⊤ ∧
    ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ d.prefixLowMaximum :=
  ⟨({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence_ne_top,
    le_finiteEnergyMaximum d.prefixLowDepths
      (fun w => ({d with t := w,i := d.i+1} : PositiveDistanceData).coincidence)
      (Finset.mem_filter.mpr ⟨hv,hvl⟩)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
