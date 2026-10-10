import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Smul
import OAI.Geometry.WeakHessian.Entropy.CompressedDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
omit [BorelSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_weighted_initial_density (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {CV : ℝ} (hVb : ∀ x,|V x| ≤ CV)
    (μ : ProbabilityMeasure X) {B : ℝ≥0} (hcap : (μ:Measure X) ≤ (B:ℝ≥0∞) • m) :
    ∃ C : ℝ≥0,∃ u : Lp ℝ 2 (exponentialMeasure m V),
      (∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x) ∧
      (∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ C) ∧
      (∫ x,u x ∂exponentialMeasure m V) = 1 ∧
      densityMeasure (exponentialMeasure m V) u = (μ:Measure X) := by
  let ν := exponentialMeasure m V
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVb
  have hnfin := hfin.of_le_smul (C := (Real.exp CV).toNNReal) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let C : ℝ≥0 := B*(Real.exp CV).toNNReal
  have hcapν : (μ:Measure X) ≤ (C:ℝ≥0∞) • ν := hcap.trans (by
    calc
      (B:ℝ≥0∞) • m ≤ (B:ℝ≥0∞) • (((Real.exp CV).toNNReal:ℝ≥0∞) • ν) := by
        gcongr
        exact hmν
      _ = (C:ℝ≥0∞) • ν := by rw [smul_smul]; rfl)
  obtain ⟨u,hun,hub,hui,hum,hul,_⟩ := exists_compressedDensity hcapν
  exact ⟨C,u,hun,hub,by simpa only [probReal_univ] using hum,hul⟩
end WeakHessian

end
end

end OAI
