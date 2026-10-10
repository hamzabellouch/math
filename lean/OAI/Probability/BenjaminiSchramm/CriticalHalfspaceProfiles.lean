import OAI.Probability.BenjaminiSchramm.CriticalCeilingProfile
import OAI.Probability.BenjaminiSchramm.CeilingDownCrudeProfile
import OAI.Probability.BenjaminiSchramm.HalfspaceProfileBootstrap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_halfspace_fractional_profiles
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∀ q : ℝ, 0 < q → q < 1 →
      (criticalModel G).downwardHalfspaceFractionalProfile
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q ∧
      (criticalModel G).upwardHalfspaceFractionalProfile
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) R q := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hfin (x : V) : ∀ᵐ ω ∂H.law (pc G), (Percolation.cluster H.ends ω x).Finite := by
    simpa only [H,criticalModel,CriticalPercolation.BondGraph.law,law] using
      critical_finite_general G hc hl hq hpc1 x
  obtain ⟨L₁,_hL₁,hprof₁⟩ := critical_lower_slab_fractional_profile G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  have hjump₂ : ∀ e v w, v ∈ G e → w ∈ G e → |H.orbitAdjustedHeight a v w| ≤ 2*R := by
    intro e v w hv hw
    exact (hjump e v w hv hw).trans (by linarith)
  obtain ⟨L₂,_hL₂,hprof₂⟩ := critical_lower_slab_fractional_profile G hc hl hq hpc1 hu μ hμ hstat
    (2*R) (by positivity) hjump₂
  obtain ⟨U,_hU,hup⟩ := H.upward_fractional_slab_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 hfin L₁ L₂ hprof₁ hprof₂
  obtain ⟨A,hA,hzero⟩ := critical_ceiling_zero_band_profile G hc hl hq hpc1 hu μ hμ hstat
    (2*R) (by positivity) hjump₂
  have hzero' : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount H.ends
          (internalEdges H.ends {v | H.orbitAdjustedHeight a x v ≤ c})
          {v | -2*R ≤ H.orbitAdjustedHeight a x v ∧ H.orbitAdjustedHeight a x v ≤ 2*R} ω x)^q ∂H.law (pc G)) ≤
            C*ENNReal.ofReal (Real.exp (A*c)) := by
    simpa only [a,H,criticalModel,CriticalPercolation.BondGraph.law,law,←neg_mul] using hzero
  obtain ⟨B,hB,hcrude⟩ := H.ceiling_down_crude_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 A hA hzero'
  obtain ⟨d,hd⟩ := exists_neighbor_card_bound G hl hq
  exact H.halfspace_fractional_profile_bootstrap hHc hl hHq μ hμ hstat hu d hd R hR hjump
    (pc G) hp0 hp1 hfin L₁ U B hB hprof₁ hup hcrude

end Percolation.BenjaminiSchramm

end

end OAI
