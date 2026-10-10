import OAI.Probability.BenjaminiSchramm.CriticalHalfspaceProfiles
import OAI.Probability.BenjaminiSchramm.UpwardCeilingProfile
import OAI.Probability.BenjaminiSchramm.FloorDownProfile

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_endpoint_fractional_profiles
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    (∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G
        (internalEdges G {v | (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ k})
        {v | k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp ((-1+ζ)*k))) ∧
    (∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G
        (internalEdges G {v | -k ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v})
        {v | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hfin (x : V) : ∀ᵐ ω ∂H.law (pc G), (Percolation.cluster H.ends ω x).Finite := by
    simpa only [H,criticalModel,CriticalPercolation.BondGraph.law,law] using
      critical_finite_general G hc hl hq hpc1 x
  have hjump₂ : ∀ e v w, v ∈ G e → w ∈ G e → |H.orbitAdjustedHeight a v w| ≤ 2*R := by
    intro e v w hv hw
    exact (hjump e v w hv hw).trans (by linarith)
  have hb := critical_halfspace_fractional_profiles G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hb₂ := critical_halfspace_fractional_profiles G hc hl hq hpc1 hu μ hμ hstat (2*R) (by positivity) hjump₂
  obtain ⟨A,hA,hzero⟩ := critical_ceiling_zero_band_profile G hc hl hq hpc1 hu μ hμ hstat
    (2*R) (by positivity) hjump₂
  have hzero' : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount H.ends
        (internalEdges H.ends {v | H.orbitAdjustedHeight a x v ≤ c})
        {v | -(2*R) ≤ H.orbitAdjustedHeight a x v ∧ H.orbitAdjustedHeight a x v ≤ 2*R} ω x)^q ∂H.law (pc G)) ≤
        C*ENNReal.ofReal (Real.exp (A*c)) := by
    simpa only [a,H,criticalModel,CriticalPercolation.BondGraph.law,law] using hzero
  have hup := H.upward_ceiling_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 hfin A hA (fun q hq0 hq1 => (hb q hq0 hq1).1) hzero'
  have hdown := H.floor_down_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 hfin (fun q hq0 hq1 => (hb q hq0 hq1).2)
    (fun q hq0 hq1 => (hb₂ q hq0 hq1).2)
  simpa only [a,H,criticalModel,CriticalPercolation.BondGraph.law,law] using And.intro hup hdown

end Percolation.BenjaminiSchramm

end

end OAI
