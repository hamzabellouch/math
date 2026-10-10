import OAI.Probability.BenjaminiSchramm.SubcriticalFullLayerProfile
import OAI.Probability.BenjaminiSchramm.LayerSecondMomentDecomposition
import OAI.Probability.BenjaminiSchramm.SubcriticalLayerConvolution

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_downward_layer_second_moment
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (k l : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, restrictedLayerCount G Set.univ
          {y | (criticalModel G).adjustedLayerIndex ((criticalModel G).stationaryOrbitWeight μ) R u x y = -(k : ℤ)} ω x *
        restrictedLayerCount G Set.univ
          {y | (criticalModel G).adjustedLayerIndex ((criticalModel G).stationaryOrbitWeight μ) R u x y = -(l : ℤ)} ω x ∂law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  obtain ⟨β,hβ,C,hC,hprofile⟩ := subcritical_full_layer_profile G hc hl hq μ hμ hstat hu R hR hjump p hp hpc
  have hprof (i : ℤ) : H.supAdjustedFullLayerMoment a R p i ≤
      ENNReal.ofReal C*expAbsLayerKernel (β-R) i := by
    simpa only [expAbsLayerKernel,ENNReal.ofReal_mul hC.le] using hprofile i
  obtain ⟨K,hK,hconv⟩ := subcritical_three_profile_uniform_bound (sub_pos.mpr hβ)
    (ENNReal.ofReal C) ENNReal.ofReal_lt_top
  refine ⟨β,hβ,K,hK,?_⟩
  intro k l x u
  exact (H.adjusted_full_layer_second_moment_bound (criticalModel_connected G hc) hl a R p x u
    (-(k : ℤ)) (-(l : ℤ))).trans
      (hconv (H.supAdjustedFullLayerMoment a R p) (H.supAdjustedFullLayerMoment a R p)
        (H.supAdjustedFullLayerMoment a R p) hprof hprof hprof k l)

end Percolation.BenjaminiSchramm

end

end OAI
