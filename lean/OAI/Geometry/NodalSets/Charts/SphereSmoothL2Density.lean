import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Map

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereSmoothL2DensityMeasurable : MeasurableSpace Base := borel Base
local instance sphereSmoothL2DensityBorel : BorelSpace Base := ⟨rfl⟩

def sphereSmoothToContinuous (d : SphereEnergyData) (u : SphereEnergySmooth d) : C(Base,ℝ) :=
  ⟨SphereEnergySmooth.toSmooth d u,(SphereEnergySmooth.toSmooth d u).property.continuous⟩

theorem sphereSmoothToContinuous_dense (d : SphereEnergyData) : DenseRange (sphereSmoothToContinuous d) := by
  rw [Metric.denseRange_iff]
  intro f eps heps
  obtain ⟨g,hg,-⟩ := f.continuous.exists_contMDiff_approx (𝓡 4) (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : Base ↦ eps/2)) (fun _ ↦ half_pos heps)
  let u : SphereEnergySmooth d := (⟨g,g.contMDiff⟩ : sphereSmoothFunctions)
  refine ⟨u,lt_of_le_of_lt ?_ (half_lt_self heps)⟩
  apply (ContinuousMap.dist_le (half_pos heps).le).mpr
  intro x
  change dist (f x) (g x) ≤ eps/2
  rw [dist_comm]
  exact (hg x).le

theorem sphereEnergyL2Linear_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Linear d) := by
  let := sphereWeightedMeasure_finite d.density d.continuous (fun x ↦ (d.positive x).le)
  have hd := (ContinuousMap.toLp_denseRange (E := ℝ) (μ := sphereWeightedMeasure d.density) (𝕜 := ℝ) (p := 2) (by simp)).comp
    (sphereSmoothToContinuous_dense d) (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ).continuous
  have heq : (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ) ∘ sphereSmoothToContinuous d =
      sphereEnergyL2Linear d := by
    funext u
    apply Lp.ext
    exact ((sphereSmoothToContinuous d u).coeFn_toLp (sphereWeightedMeasure d.density)).trans
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp.symm
  rwa [heq] at hd

theorem sphereEnergyL2Map_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Map d) := by
  apply (sphereEnergyL2Linear_dense d).mono
  rintro _ ⟨u,rfl⟩
  exact ⟨sphereEnergyToCompletion d u,sphereEnergyL2Map_coe d u⟩

end
end Yau.Target

end OAI
