import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

/-! One finite measure dominates every member of a countable family of
finite spectral measures. The Radon–Nikodym densities give common coordinates. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (ν : ι → Measure Ω)
  [∀ n, IsFiniteMeasure (ν n)]

def commonSpectralMeasure : Measure Ω := (Measure.sum ν).toFinite

instance commonSpectralMeasure_finite : IsFiniteMeasure (commonSpectralMeasure ν) :=
  inferInstanceAs (IsFiniteMeasure (Measure.sum ν).toFinite)

theorem component_absolutelyContinuous_common (n : ι) :
    ν n ≪ commonSpectralMeasure ν :=
  (Measure.absolutelyContinuous_sum_right n (Measure.AbsolutelyContinuous.refl (ν n))).trans
    (absolutelyContinuous_toFinite (Measure.sum ν))

theorem component_density_common (n : ι) :
    (commonSpectralMeasure ν).withDensity ((ν n).rnDeriv (commonSpectralMeasure ν)) = ν n :=
  Measure.withDensity_rnDeriv_eq _ _ (component_absolutelyContinuous_common ν n)

end KadisonSimilarity

end

end OAI
