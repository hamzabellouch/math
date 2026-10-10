import OAI.Probability.BenjaminiSchramm.CriticalPeakSurvival
import OAI.Probability.BenjaminiSchramm.UpwardFractionalSlabProfile

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_lower_slab_fractional_profile
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℝ, 0 < L ∧ (criticalModel G).lowerSlabFractionalProfile
      ((criticalModel G).stationaryOrbitWeight μ) (pc G) R L := by
  let O := (criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq)
  obtain ⟨α,hα,hcross,hsurv⟩ := critical_crossing_and_peak_survival G hc hl hq hpc1 hu
    μ hμ hstat R hR hjump O
  obtain ⟨L,hL,hbound⟩ := critical_slab_fractional_of_peak_survival G hc hl hq hpc1 hu
    μ hμ hstat α hα hcross R hR hjump hsurv
  refine ⟨L,hL,fun q hq0 hq1 ζ hζ => ?_⟩
  obtain ⟨C,hC,hb⟩ := hbound q hq0 hq1 ζ hζ
  refine ⟨C,hC,fun k hk r hr x => ?_⟩
  simpa only [CriticalPercolation.BondGraph.adjustedSlabBandCount_eq_restricted,
    criticalModel,CriticalPercolation.BondGraph.law,law] using hb k hk r hr x

end Percolation.BenjaminiSchramm

end

end OAI
