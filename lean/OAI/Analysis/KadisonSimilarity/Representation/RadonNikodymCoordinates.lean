import OAI.Analysis.KadisonSimilarity.Representation.CommonSpectralMeasure
import OAI.Analysis.KadisonSimilarity.Representation.SpectralDensityIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Square-root Radon–Nikodym coordinates put each finite scalar spectral
measure over a common finite base. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] (μ ν : Measure X)

def squareRootDensity (x : X) : ℝ≥0 := NNReal.sqrt ((ν.rnDeriv μ x).toNNReal)

theorem squareRootDensity_measurable : Measurable (squareRootDensity μ ν) :=
  NNReal.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv ν μ).ennreal_toNNReal

theorem squareRootDensity_sq_ae [SigmaFinite μ] [SigmaFinite ν] :
    (fun x => ((squareRootDensity μ ν x) ^ 2 : ℝ≥0∞)) =ᵐ[μ] ν.rnDeriv μ := by
  filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
  simp only [squareRootDensity, ← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_toNNReal hx.ne]

theorem squaredDensityMeasure_eq [SigmaFinite μ] [SigmaFinite ν] (hν : ν ≪ μ) :
    squaredDensityMeasure μ (squareRootDensity μ ν) = ν := by
  calc
    _ = μ.withDensity (ν.rnDeriv μ) :=
      withDensity_congr_ae (squareRootDensity_sq_ae μ ν)
    _ = ν := Measure.withDensity_rnDeriv_eq _ _ hν

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem squareRootDensity_memLp (hν : ν ≪ μ) :
    MemLp (fun x => (squareRootDensity μ ν x : ℂ)) 2 μ := by
  have he := squaredDensityMeasure_eq μ ν hν
  have hνfin : IsFiniteMeasure ν := inferInstance
  let : IsFiniteMeasure (squaredDensityMeasure μ (squareRootDensity μ ν)) := he.symm ▸ hνfin
  exact weight_memLp_of_finite_squareDensity μ (squareRootDensity μ ν)
    (squareRootDensity_measurable μ ν)

section Topology
variable [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X]
  [ν.WeaklyRegular]

/-- The actual scalar L² coordinate inclusion over a dominating measure. -/
def radonNikodymIsometry (hν : ν ≪ μ) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  spectralDensityIsometryOfEq μ (squareRootDensity μ ν) (squareRootDensity_measurable μ ν)
    (squareRootDensity_memLp μ ν hν) ν (squaredDensityMeasure_eq μ ν hν)

theorem radonNikodymIsometry_toLp (hν : ν ≪ μ) (f : C(X, ℂ)) :
    spectralDensityIsometryOfEq μ (squareRootDensity μ ν)
      (squareRootDensity_measurable μ ν) (squareRootDensity_memLp μ ν hν) ν
      (squaredDensityMeasure_eq μ ν hν) (ContinuousMap.toLp 2 ν ℂ f) =
        weightedContinuousVector μ (squareRootDensity μ ν) (squareRootDensity_measurable μ ν)
          (squareRootDensity_memLp μ ν hν) f :=
  spectralDensityIsometryOfEq_toLp μ (squareRootDensity μ ν)
    (squareRootDensity_measurable μ ν) (squareRootDensity_memLp μ ν hν) ν
    (squaredDensityMeasure_eq μ ν hν) f


end Topology
end KadisonSimilarity

end

end OAI
