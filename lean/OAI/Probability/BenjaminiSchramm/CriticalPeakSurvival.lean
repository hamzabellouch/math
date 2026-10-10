import OAI.Probability.BenjaminiSchramm.PeakSprinklingSurvival
import OAI.Probability.BenjaminiSchramm.SprinklingAvoidanceProfile
import OAI.Probability.BenjaminiSchramm.SprinklingParameter
import OAI.Probability.BenjaminiSchramm.SubcriticalPeakConditional
import OAI.Probability.BenjaminiSchramm.CrossingExponentContinuity
import OAI.Probability.BenjaminiSchramm.LayerCrossingComparison
import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness
import OAI.Probability.BenjaminiSchramm.NormalizedExponentComparison
import OAI.Probability.BenjaminiSchramm.AntitoneSurvivalHeight

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma fullPeakDownProbability_antitone (O : G.OrbitRepresentatives) (a : V → ℝ)
    (p : unitInterval) : Antitone (G.fullPeakDownProbability O a p) := by
  intro ell ell' hle
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro ω ⟨hpeak,y,hy,hxy⟩
  change G.orbitAdjustedHeight a x y ≤ -ell' at hy
  exact ⟨hpeak,y,show G.orbitAdjustedHeight a x y ≤ -ell by linarith,hxy⟩

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_peak_survival_eventual
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (O : (criticalModel G).OrbitRepresentatives) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*Real.exp (-(R*(α-1)+ε)*n)) ≤
        (criticalModel G).fullPeakDownProbability O
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) (R*n) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have ha := H.stationaryOrbitWeight_aut μ
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  obtain ⟨q,hqhalf,hqpc,γ,hγ,hγα,_hγupper,hγlower⟩ :=
    H.normalized_crossing_exponent_approximation hHc hl hHq μ hμ hstat hu
      (pc G) hp α hlim (ε/(2*R)) (div_pos hε (by positivity))
  have hqpos : (0 : ℝ) < q := (half_pos hp).trans_le hqhalf
  obtain ⟨β,hβR,K,hK,hup,c,hcpos,C,hC,hprofile⟩ :=
    subcritical_weighted_peak_conditional_layers G hc hl hq μ hμ hstat hu R hR hjump
      q hqpos hqpc O
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq q hqpc
  have hβγ : β ≤ γ*R := by
    apply H.crossing_rate_ge_layer_rate hHc hl a R hR hjump q
      (ENNReal.ofReal χ) ENNReal.ofReal_lt_top hrow γ β hγ hγlower
    intro δ hδ
    refine ⟨K,hK,fun n => (hup n).trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨b,hb0,hb1,hparam⟩ := exists_sprinkling_parameter q (pc G) hqpc hpc1
  have hfincrit (x : V) : ∀ᵐ ω ∂H.law (pc G), (H.cluster ω x).Finite := by
    simpa only [H,criticalModel_cluster,CriticalPercolation.BondGraph.law,law] using
      critical_finite_general G hc hl hq hpc1 x
  have hfinq (x : V) : ∀ᵐ ω ∂H.law q, (H.cluster ω x).Finite := by
    simpa only [H,criticalModel_cluster,CriticalPercolation.BondGraph.law,law] using
      subcritical_cluster_finite_ae G q hqpc x
  obtain ⟨d,_hdpos,hd⟩ := exists_degree_bound G hq
  obtain ⟨g,hg,⟨C₀,hgb⟩,hglim,havoid⟩ := H.sprinkling_avoidance_cost_profile
    hHc hl O a ha (pc G) q b hparam hb0 hb1 R hR d hd hfincrit
  have hC₀ : 0 ≤ C₀ := (hg 0).trans (hgb 0)
  have hsurv := H.peak_sprinkling_eventual_survival hHc hl O (pc G) q b hparam
    a R hR hfinq g hg C₀ hC₀ hgb hglim havoid c (β-R) (β-R) C
      (sub_pos.mpr hβR) hC.le (fun n hn => (hprofile n hn).1)
      (fun n hn => (hprofile n hn).2) (ε/2) (half_pos hε)
  have hrate : β-R+ε/2 ≤ R*(α-1)+ε := by
    have hh := (lt_div_iff₀ (show 0 < 2*R by positivity)).mp
      (show γ-α < ε/(2*R) by linarith)
    nlinarith
  refine ⟨c/2,half_pos hcpos,?_⟩
  filter_upwards [hsurv] with n hn
  apply le_trans _ hn
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (half_pos hcpos).le
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem critical_peak_survival_real
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hα : 1 ≤ α)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
      ENNReal.ofReal (c*Real.exp (-((α-1)+ε)*ell)) ≤
        (criticalModel G).fullPeakDownProbability O
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell := by
  apply antitone_survival_real_lower _
    ((criticalModel G).fullPeakDownProbability_antitone O _ _) R (α-1) hR (by linarith)
  exact critical_peak_survival_eventual G hc hl hq hpc1 hu μ hμ hstat α hlim R hR hjump O

theorem critical_crossing_and_peak_survival
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∃ α : ℝ, 1 ≤ α ∧
      (∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
        ENNReal.ofReal (c*Real.exp (-((α-1)+ε)*ell)) ≤
          (criticalModel G).fullPeakDownProbability O
            ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell) := by
  obtain ⟨α,hα,hupper,_hlower,hlim⟩ :=
    critical_normalized_exact_exponent G hc hl hq hu μ hμ hstat
  exact ⟨α,hα,hupper,critical_peak_survival_real G hc hl hq hpc1 hu μ hμ hstat
    α hα hlim R hR hjump O⟩

end Percolation.BenjaminiSchramm

end

end OAI
