import OAI.Probability.BenjaminiSchramm.CriticalSlabProfiles
import OAI.Probability.BenjaminiSchramm.CeilingZeroBand
import OAI.Probability.BenjaminiSchramm.NeighborDegreeBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_ceiling_zero_band_profile
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G
        (internalEdges G {v | (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ c})
        {v | -R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x v ≤ R} ω x)^q ∂law (pc G)) ≤
          C*ENNReal.ofReal (Real.exp (A*c)) := by
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
  obtain ⟨T,hT,hshift⟩ := H.finite_ceiling_fractional_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 L₁ hprof₁
  obtain ⟨U,hU,hup⟩ := H.upward_fractional_slab_profile hHc hl hHq μ hμ hstat hu R hR hjump
    (pc G) hp0 hp1 hfin L₁ L₂ hprof₁ hprof₂
  obtain ⟨d,hd⟩ := exists_neighbor_card_bound G hl hq
  have hh := H.ceiling_zero_band_from_profiles hHc hl a d hd R hR hjump (pc G) hfin T U hT hU
    (fun q hq0 hq1 ζ hζ hζ1 => by
      obtain ⟨C,hC,hb⟩ := hshift q hq0 hq1 ζ hζ hζ1
      refine ⟨C,hC,fun k hk c hc0 x => ?_⟩
      simpa only [sub_zero,mul_zero,add_zero] using hb k hk 0 (by norm_num) c hc0 x) hup
  refine ⟨T+U+1,by positivity,fun q hq0 hq1 => ?_⟩
  obtain ⟨C,hC,hb⟩ := hh q hq0 hq1
  refine ⟨C,hC,fun c hc0 x => ?_⟩
  simpa only [a,H,criticalModel,CriticalPercolation.BondGraph.law,law] using hb c hc0 x

end Percolation.BenjaminiSchramm

end

end OAI
