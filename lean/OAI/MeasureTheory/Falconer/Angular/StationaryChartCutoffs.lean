import OAI.MeasureTheory.Falconer.Angular.StationarySineChart
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryCutoff : ContDiffBump (0:ℝ) :=
  ⟨1/2,1,by norm_num,by norm_num⟩
noncomputable def stationaryChartCutoff : ContDiffBump (0:ℝ) :=
  ⟨1,3/2,by norm_num,by norm_num⟩

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

noncomputable def extendedStationaryInverse (u : ℝ) : ℝ :=
  stationaryChartCutoff u * stationarySineInverse u
noncomputable def stationaryWeight (u : ℝ) : ℝ :=
  stationaryCutoff u * stationarySineJacobian u

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

 theorem stationaryWeight_tsupport : tsupport stationaryWeight ⊆ Icc (-1:ℝ) 1 := by
  exact tsupport_mul_subset_left.trans stationaryCutoff_tsupport.subset

 theorem extendedStationaryInverse_tsupport :
    tsupport extendedStationaryInverse ⊆ Icc (-3/2:ℝ) (3/2) := by
  exact tsupport_mul_subset_left.trans stationaryChartCutoff_tsupport.subset

end PlanarFalconer

end OAI
