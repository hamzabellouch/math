import OAI.Analysis.CircleDomains.Sobolev.CoareaSummableErrors
import OAI.Analysis.CircleDomains.Sobolev.L2WeightedErrorSeries
import OAI.Analysis.CircleDomains.Sobolev.SobolevCoareaFiniteLevels

namespace OAI

/-! Summable strong Sobolev errors vanish on almost every full level,
with the exceptional values independent of any later arc or component. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_L2_errors
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Measurable (f n))
    (hL : ∀ n, MemLp (f n) 2 (volume.restrict E))
    (hs : Summable (fun n => (eLpNorm (f n) 2 (volume.restrict E)).toReal)) :
    ∀ᵐ t ∂volume,
      Tendsto (fun n => sobolevLevelIntegral E v (fun p => ENNReal.ofReal ‖f n p‖) t)
        atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  have hsum := weighted_L2_errors_summable f hL hV.norm hs
  have hh := coarea_summable_errors hcoarea hv hw hLp hE hb
    (fun n p => ENNReal.ofReal ‖f n p‖)
    (fun n => ENNReal.measurable_ofReal.comp (hf n).norm) (by simpa only [norm_norm] using hsum)
  exact hh.mono (fun _ h => h.2)

end CircleDomainRigidity

end

end OAI
