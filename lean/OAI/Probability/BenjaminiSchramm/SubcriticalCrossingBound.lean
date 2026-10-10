import OAI.Probability.BenjaminiSchramm.LayerCrossingComparison
import OAI.Probability.BenjaminiSchramm.MinimumHeightHit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem unrestricted_upward_bound_of_layer_rate
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (C : ℝ≥0∞) (hC : C < ⊤)
    (hrow : ∀ z, (∑' y, law p {ω | Conn G ω z y}) ≤ C)
    (β : ℝ)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (criticalModel G).supAdjustedUpLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p n ≤
        ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (x : V),
      law p (restrictedHit G Set.univ x
        {y | R*((n : ℝ)-1) ≤ (criticalModel G).orbitAdjustedHeight
          ((criticalModel G).stationaryOrbitWeight μ) x y}) ≤ ENNReal.ofReal (B*Real.exp (-β*n)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨α,hα,hαupper,hαlower,_hαlim⟩ := H.normalized_crossing_exponent hHc hl hHq μ hμ hstat hu p hp
  have hβα := H.crossing_rate_ge_layer_rate hHc hl a R hR hjump p C hC hrow α β hα hαlower hupper
  have hreal := normalized_crossing_real_bound G hc hl hq μ hμ p α hα hαupper
  obtain ⟨A,D,_hA,_hD,hroot⟩ := normalized_halfspace_uniform_of_infimal_bound G hc hl hq hu μ hμ hstat p hp α hreal
  let K : ℝ := (p : ℝ)^(-D)
  have hK : 0 < K := Real.rpow_pos_of_pos hp _
  let B := 1+C.toReal*K*Real.exp (α*R)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,fun n x => ?_⟩
  by_cases hn : n=0
  · subst n
    have hB1 : (1 : ℝ) ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (by positivity)
    simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using
      (prob_le_one (μ := law p)).trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hB1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have ht : 0 ≤ R*((n : ℝ)-1) := mul_nonneg hR.le (by linarith)
  have hκ (z : V) : H.law p (H.adjustedHalfspaceHit a z 0 (R*((n : ℝ)-1))) ≤
      ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
    have hh := hroot 0 (le_refl 0) z (R*((n : ℝ)-1)) ht
    simp only [mul_zero,zero_add,neg_zero] at hh
    have he := ENNReal.ofReal_le_ofReal hh
    change ENNReal.ofReal ((H.law p (H.adjustedHalfspaceHit a z 0 (R*((n : ℝ)-1)))).toReal) ≤
      ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) at he
    rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  have hh := H.unrestricted_adjusted_upward_hit_bound hHc hl a p C _ hrow _ hκ x
  have hexp : Real.exp (-α*(R*((n : ℝ)-1))) ≤ Real.exp (α*R)*Real.exp (-β*n) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc
    _ ≤ C*ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := hh
    _ = ENNReal.ofReal (C.toReal*K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
      calc
        _ = ENNReal.ofReal C.toReal*ENNReal.ofReal (K*Real.exp (-α*(R*((n : ℝ)-1)))) := by
          rw [ENNReal.ofReal_toReal hC.ne]
        _ = _ := by rw [←ENNReal.ofReal_mul ENNReal.toReal_nonneg]; congr 1; ring
    _ ≤ ENNReal.ofReal ((C.toReal*K*Real.exp (α*R))*Real.exp (-β*n)) := by
      apply ENNReal.ofReal_le_ofReal
      have he := mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ C.toReal*K from mul_nonneg ENNReal.toReal_nonneg hK.le)
      simpa only [mul_assoc] using he
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [B]
      linarith

end Percolation.BenjaminiSchramm

end

end OAI
