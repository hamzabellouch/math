import OAI.Probability.BenjaminiSchramm.PeakConditionalLayers

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma exponential_max_factorization (a c D n l : ℝ) (hc : c ≠ 0) :
    D*Real.exp (-a*max n l)=
      (c*Real.exp (-a*n))*((D/c)*Real.exp (-a*max (l-n) 0)) := by
  have hm : max n l=n+max (l-n) 0 := by
    rcases le_total n l with h | h
    · rw [max_eq_right h,max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left h,max_eq_right (sub_nonpos.mpr h)]
      ring
  rw [hm]
  calc
    _ = D*(Real.exp (-a*n)*Real.exp (-a*max (l-n) 0)) := by
      rw [←Real.exp_add]
      congr 2
      ring
    _ = _ := by field_simp

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_weighted_peak_conditional_layers
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
      ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        ENNReal.ofReal (c*Real.exp (-(β-R)*n)) ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n ∧
        ∀ l : ℕ, (criticalModel G).peakSurvivalLayerMoment O
          ((criticalModel G).stationaryOrbitWeight μ) R p n l ≤
          (criticalModel G).peakSurvivalProbability O ((criticalModel G).stationaryOrbitWeight μ) R p n *
            ENNReal.ofReal (C*Real.exp (-(β-R)*max ((l : ℝ)-n) 0)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  obtain ⟨β,hβR,K,hK,hup,c,hcpos,hsurv⟩ := subcritical_weighted_peak_survival G hc hl hq
    μ hμ hstat hu R hR hjump p hp hpc O
  obtain ⟨C₀,hC₀,hprofile⟩ := subcritical_full_layer_profile_at_rate G hc hl hq μ hμ
    R hR hjump p hpc β K hβR hK hup
  obtain ⟨K₂,hK₂,hsecond⟩ := H.adjusted_downward_layer_second_moment_at_rate
    hHc hl a R p β C₀ hβR hC₀ hprofile
  let B : ℝ≥0∞ := (∑ x ∈ O.roots, ENNReal.ofReal (a x))*(4*K₂)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by norm_num) hK₂.ne)
  let D := B.toReal+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ ENNReal.ofReal D := by
    rw [←ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
  refine ⟨β,hβR,K,hK,hup,c,hcpos,D/c,div_pos hD hcpos,?_⟩
  intro n hn
  refine ⟨hsurv n hn,?_⟩
  intro l
  calc
    _ ≤ B*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) :=
      H.peakSurvivalLayerMoment_bound O hHc hl a R hR p β hβR K₂
        (fun k j x => hsecond k j x 0) n l
    _ ≤ ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-(β-R)*((max n l : ℕ) : ℝ))) :=
      mul_le_mul' hBD le_rfl
    _ = ENNReal.ofReal (c*Real.exp (-(β-R)*n))*
        ENNReal.ofReal ((D/c)*Real.exp (-(β-R)*max ((l : ℝ)-n) 0)) := by
      rw [←ENNReal.ofReal_mul hD.le,←ENNReal.ofReal_mul
        (mul_nonneg hcpos.le (Real.exp_nonneg _))]
      congr 1
      rw [Nat.cast_max]
      exact exponential_max_factorization (β-R) c D n l hcpos.ne'
    _ ≤ _ := mul_le_mul' (hsurv n hn) le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
