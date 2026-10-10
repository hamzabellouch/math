import OAI.Probability.BenjaminiSchramm.SubcriticalPeakProbability
import OAI.Probability.BenjaminiSchramm.PeakSurvivalCauchy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_weighted_peak_survival
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G)
    (O : (criticalModel G).OrbitRepresentatives) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
        ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
          ∑ x ∈ O.roots, ENNReal.ofReal ((criticalModel G).stationaryOrbitWeight μ x)*
            (criticalModel G).law p {ω | 0 < (criticalModel G).peakDownBandCount
              ((criticalModel G).stationaryOrbitWeight μ) (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x} := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hapos := H.stationaryOrbitWeight_pos hHc hl μ hμ
  have ha := H.stationaryOrbitWeight_aut μ
  obtain ⟨β,hβR,K,hK,hup,c,hcpos,hpeak⟩ := subcritical_peak_band_probability G hc hl hq
    μ hμ hstat hu R hR hjump p hp hpc
  obtain ⟨m,_M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨C,hC,hprofile⟩ := subcritical_full_layer_profile_at_rate G hc hl hq μ hμ
    R hR hjump p hpc β K hβR hK hup
  obtain ⟨K₂,hK₂,hsecond⟩ := H.adjusted_downward_layer_second_moment_at_rate hHc hl a R p β C hβR hC hprofile
  let c₁ := m*c*Real.exp R
  have hc₁ : 0 < c₁ := mul_pos (mul_pos hm hcpos) (Real.exp_pos _)
  let B : ℝ≥0∞ := (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(16*K₂)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
  let D := B.toReal+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ ENNReal.ofReal D := by
    rw [←ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
  refine ⟨β,hβR,K,hK,hup,c₁^2/D,div_pos (sq_pos_of_pos hc₁) hD,?_⟩
  intro n hn
  let l := R*((n : ℝ)+1)
  let u := R*((n : ℝ)+4)
  let t := Real.exp (-(β-R)*n)
  have ht : 0 < t := Real.exp_pos _
  have hpweighted : ENNReal.ofReal (m*c*Real.exp (-β*n)) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*H.law p (H.strictPeakBandEvent a l u x) := by
    obtain ⟨x,hx⟩ := hpeak n hn
    calc
      _ = ENNReal.ofReal m*ENNReal.ofReal (c*Real.exp (-β*n)) := by
        rw [←ENNReal.ofReal_mul hm.le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal m*H.law p (H.strictPeakBandEvent a l u x) := mul_le_mul' le_rfl hx
      _ ≤ _ := H.strictPeakBandEvent_probability_le_weighted_roots O a ha m
        (fun x => (hweights x).1) p l u x
  have hfirst : ENNReal.ofReal (c₁*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, H.peakDownBandCount a l u ω x ∂H.law p) := by
    have heq : ENNReal.ofReal (c₁*t)=
        ENNReal.ofReal (Real.exp l)*ENNReal.ofReal (m*c*Real.exp (-β*n)) := by
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      change m*c*Real.exp R*Real.exp (-(β-R)*(n : ℝ))=
        Real.exp (R*((n : ℝ)+1))*(m*c*Real.exp (-β*n))
      calc
        _ = m*c*(Real.exp R*Real.exp (-(β-R)*(n : ℝ))) := by ring
        _ = m*c*Real.exp (R+ -(β-R)*(n : ℝ)) := by rw [Real.exp_add]
        _ = _ := by
          rw [show R+ -(β-R)*(n : ℝ)=R*((n : ℝ)+1)+ -β*n by ring,Real.exp_add]
          ring
    rw [heq]
    apply (mul_le_mul' le_rfl (hpweighted.trans
      (H.expected_peakDownBandCount_lower O hHc hl a hapos ha p l u))).trans_eq
    rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
      add_neg_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul]
  have hsec (x : V) : (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p) ≤ (16*K₂)*ENNReal.ofReal t := by
    exact H.peakDownBandCount_second_moment_bound hHc hl a R hR p β hβR K₂
      (fun k j x => hsecond k j x 0) n x
  have hsecfin (x : V) : (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
      ENNReal.ofReal_ne_top) (hsec x)
  have hsectotal : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
      (∫⁻ ω, (H.peakDownBandCount a l u ω x)^2 ∂H.law p)) ≤ ENNReal.ofReal (D*t) := by
    calc
      _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*((16*K₂)*ENNReal.ofReal t) :=
        Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (hsec x)
      _ = B*ENNReal.ofReal t := by rw [←Finset.sum_mul]; dsimp [B]; ring
      _ ≤ ENNReal.ofReal D*ENNReal.ofReal t := mul_le_mul' hBD le_rfl
      _ = _ := (ENNReal.ofReal_mul hD.le).symm
  exact H.peakDownBandCount_probability_lower_of_moments O a l u p _ ENNReal.ofReal_ne_top
    hrow c₁ D t hc₁ hD ht hfirst (fun x _ => hsecfin x) hsectotal

end Percolation.BenjaminiSchramm

end

end OAI
