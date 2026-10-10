import OAI.Probability.BenjaminiSchramm.LayerPrefactorBootstrap
import OAI.Probability.BenjaminiSchramm.SubcriticalCrossingBound
import OAI.Probability.BenjaminiSchramm.BandMomentSummability
import OAI.Probability.BenjaminiSchramm.SignedUpperConvolution

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_layer_prefactor
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G) :
    ∃ β : ℝ, R < β ∧
      (∀ n : ℕ, ENNReal.ofReal (Real.exp (-β*n)) ≤
        (criticalModel G).supAdjustedUpLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p n) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        (criticalModel G).supAdjustedUpLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p n ≤
          ENNReal.ofReal (K*Real.exp (-β*n)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  let C := ENNReal.ofReal χ
  have hC : C < ⊤ := ENNReal.ofReal_lt_top
  have hSbound (n : ℕ) : H.supAdjustedUpLayerMoment a R p n ≤ C := by
    apply iSup_le
    intro x
    apply iSup_le
    intro u
    exact restrictedLayerCount_expectation_le_row_bound G p C hrow _ _ x
  have hne (n : ℕ) : H.supAdjustedUpLayerMoment a R p n ≠ ⊤ := (lt_of_le_of_lt (hSbound n) hC).ne
  let S : ℕ → ℝ := fun n => (H.supAdjustedUpLayerMoment a R p n).toReal
  have hS (n : ℕ) : 0 ≤ S n := ENNReal.toReal_nonneg
  have hSEq (n : ℕ) : ENNReal.ofReal (S n)=H.supAdjustedUpLayerMoment a R p n := ENNReal.ofReal_toReal (hne n)
  have hSb (n : ℕ) : S n ≤ χ := by
    have hh := ENNReal.toReal_mono hC.ne (hSbound n)
    rwa [ENNReal.toReal_ofReal hχ] at hh
  obtain ⟨β,_hβ,hlower,hupper,_hlim⟩ := H.subcritical_normalized_layer_rate hHc hl hHq hq
    μ hμ hstat hu R hR hjump p hp hpc
  have hlo (n : ℕ) : ENNReal.ofReal (Real.exp (-β*n)) ≤ H.supAdjustedUpLayerMoment a R p n := by
    have hh := ENNReal.ofReal_le_ofReal (hlower n)
    rwa [ENNReal.ofReal_toReal (hne n)] at hh
  obtain ⟨m,M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  have hβR : R < β := H.normalized_layer_rate_strict_of_lower (H.orbitRepresentatives hHq)
    hHc hl a (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ)
      m hm (fun x => (hweights x).1) R hR p C hC hrow β hlo
  have hβ : 0 < β := hR.trans hβR
  obtain ⟨K,hK,hKbd⟩ := hupper (β/4) (by positivity)
  have hdecay (n : ℕ) : S n ≤ K*Real.exp (-(3*β/4)*n) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKbd n)
    rw [ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _))] at hh
    convert hh using 1
    congr 2
    ring
  have hmul (n j : ℕ) : S (n+j) ≤ S n*S j := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hne n) (hne j))
      (H.supAdjustedUpLayerMoment_submultiplicative hHc hl a R hR hjump p n j)
    simpa only [ENNReal.toReal_mul] using hh
  have hF (i : ℤ) : H.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    H.supAdjustedFullLayerMoment_le_row_bound a R p C hrow i
  have hFpos (i : ℕ) : H.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal (χ*S i) := by
    apply (H.supAdjustedFullLayerMoment_up_bound hHc hl a R hR hjump p C hrow i).trans_eq
    rw [←hSEq i]
    change ENNReal.ofReal (S i)*ENNReal.ofReal χ=ENNReal.ofReal (χ*S i)
    rw [←ENNReal.ofReal_mul (hS i)]
    congr 1
    ring
  obtain ⟨A,hA,hsecondbd⟩ := signed_upper_convolution_bound S hS β K χ hβ hχ hSb hmul hdecay
    (H.supAdjustedFullLayerMoment a R p) hF hFpos
  have hsecond (n : ℕ) (x : V) (u : ℝ) :
      (∫⁻ ω, (restrictedLayerCount G
        (internalEdges G {y | H.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
        {y | H.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n) := by
    apply (H.adjusted_upper_layer_second_moment_bound hHc hl a R p x u n).trans
    simpa only [hSEq] using hsecondbd n
  obtain ⟨B,hB,hprob⟩ := unrestricted_upward_bound_of_layer_rate G hc hl hq μ hμ hstat hu
    R hR hjump p hp C hC hrow β hupper
  refine ⟨β,hβR,hlo,A*B,mul_pos hA hB,?_⟩
  exact H.adjusted_layer_prefactor_bootstrap a R hR p β A B hA.le hB.le hne hprob hsecond

end Percolation.BenjaminiSchramm

end

end OAI
