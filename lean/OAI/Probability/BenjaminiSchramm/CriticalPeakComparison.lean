import OAI.Probability.BenjaminiSchramm.WeightedPeakSlabComparison
import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_peak_comparison
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∃ L : ℝ, 0 < L ∧
      ∀ k, 0 ≤ k → ∀ r, 0 ≤ r → ∀ ell, 0 < ell → ∀ v₀,
      (criticalModel G).fullPeakDownProbability
        ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell*
      (criticalModel G).mixedHeightLayerMoment ((criticalModel G).stationaryOrbitWeight μ)
        (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
          K*ENNReal.ofReal (Real.exp (L*r)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨N,M,hM,hpaths⟩ := H.stationaryOrbitHeight_bounded_orbit_below hHc hl
    (criticalModel_quasiTransitive G hq) μ hμ hstat hu R hR hjump
  obtain ⟨d,_hdpos,hd⟩ := exists_degree_bound G hq
  obtain ⟨C,L,hC,hL,hband⟩ := critical_peak_band_bound G hc hl hq hu μ hμ hstat
  let cost := ENNReal.ofReal ((min (pc G : ℝ) (1-pc G))^(d*(N+1)))
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hcost0 : cost ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact pow_pos (lt_min hp0 (sub_pos.mpr hp1)) _
  have hcosttop : cost ≠ ⊤ := ENNReal.ofReal_ne_top
  let W := ∑ x ∈ O.roots, ENNReal.ofReal (a x)
  let K := cost⁻¹*W*ENNReal.ofReal (C*Real.exp (L*(R+M)+M+2*R))
  have hW : W < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hcost0)) hW) ENNReal.ofReal_lt_top
  refine ⟨M,hM,K,hK,L,hL,fun k hk r hr ell hell v₀ => ?_⟩
  have hcmp := H.weighted_full_peak_lower_slab_comparison O hHc hl a
    (H.stationaryOrbitWeight_aut μ) d N hd (pc G) R M k r ell hR.le hM.le hk hr hell
    hjump hpaths (critical_finite_general G hc hl hq hpc1) v₀
  have hbound := hband (r+R+M) (by positivity) (-ell-k-M-2*R) (-ell-k) (by linarith)
  have hcancel : cost⁻¹*cost=1 := ENNReal.inv_mul_cancel hcost0 hcosttop
  calc
    _ = cost⁻¹*((H.fullPeakDownProbability O a (pc G) ell*cost)*
        H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀) := by
      let P := H.fullPeakDownProbability O a (pc G) ell
      let X := H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀
      change P*X=cost⁻¹*((P*cost)*X)
      calc
        _ = (cost⁻¹*cost)*(P*X) := by rw [hcancel,one_mul]
        _ = _ := by ac_rfl
    _ ≤ cost⁻¹*(W*ENNReal.ofReal (C*Real.exp (L*(r+R+M)+(-ell-k)-(-ell-k-M-2*R)))) :=
      mul_le_mul' le_rfl (hcmp.trans hbound)
    _ = K*ENNReal.ofReal (Real.exp (L*r)) := by
      have he : C*Real.exp (L*(r+R+M)+(-ell-k)-(-ell-k-M-2*R)) =
          (C*Real.exp (L*(R+M)+M+2*R))*Real.exp (L*r) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
      rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ C*Real.exp (L*(R+M)+M+2*R))]
      dsimp [K]
      ac_rfl

theorem critical_peak_comparison_at_rate
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ M : ℝ, 0 < M ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧ ∃ L : ℝ, 0 < L ∧
      ∀ k, 0 ≤ k → ∀ r, 0 ≤ r → ∀ ell, 0 < ell → ∀ v₀,
      (criticalModel G).fullPeakDownProbability
        ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell*
      (criticalModel G).mixedHeightLayerMoment ((criticalModel G).stationaryOrbitWeight μ)
        (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
          K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k))) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  have hHc := criticalModel_connected G hc
  obtain ⟨N,M,hM,hpaths⟩ := H.stationaryOrbitHeight_bounded_orbit_below hHc hl
    (criticalModel_quasiTransitive G hq) μ hμ hstat hu R hR hjump
  obtain ⟨d,_hdpos,hd⟩ := exists_degree_bound G hq
  obtain ⟨C,L,hC,hL,hband⟩ := critical_peak_band_bound_at_rate G hc hl hq hu μ hμ hstat α hcross
  let cost := ENNReal.ofReal ((min (pc G : ℝ) (1-pc G))^(d*(N+1)))
  have hp0 : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  have hp1 : (pc G : ℝ) < 1 := by exact_mod_cast hpc1
  have hcost0 : cost ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact pow_pos (lt_min hp0 (sub_pos.mpr hp1)) _
  have hcosttop : cost ≠ ⊤ := ENNReal.ofReal_ne_top
  let W := ∑ x ∈ O.roots, ENNReal.ofReal (a x)
  let K := cost⁻¹*W*ENNReal.ofReal (C*Real.exp (L*(R+M)+M+2*R))
  have hW : W < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hcost0)) hW) ENNReal.ofReal_lt_top
  refine ⟨M,hM,K,hK,L,hL,fun k hk r hr ell hell v₀ => ?_⟩
  have hcmp := H.weighted_full_peak_lower_slab_comparison O hHc hl a
    (H.stationaryOrbitWeight_aut μ) d N hd (pc G) R M k r ell hR.le hM.le hk hr hell
    hjump hpaths (critical_finite_general G hc hl hq hpc1) v₀
  have hbound := hband (r+R+M) (by positivity) (-ell-k-M-2*R) (-ell-k) (by linarith)
  have hcancel : cost⁻¹*cost=1 := ENNReal.inv_mul_cancel hcost0 hcosttop
  calc
    _ = cost⁻¹*((H.fullPeakDownProbability O a (pc G) ell*cost)*
        H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀) := by
      let P := H.fullPeakDownProbability O a (pc G) ell
      let X := H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀
      change P*X=cost⁻¹*((P*cost)*X)
      calc
        _ = (cost⁻¹*cost)*(P*X) := by rw [hcancel,one_mul]
        _ = _ := by ac_rfl
    _ ≤ cost⁻¹*(W*ENNReal.ofReal (C*Real.exp (L*(r+R+M)+α*(-ell-k)-(-ell-k-M-2*R)))) :=
      mul_le_mul' le_rfl (hcmp.trans hbound)
    _ = K*ENNReal.ofReal (Real.exp (L*r-(α-1)*(ell+k))) := by
      have he : C*Real.exp (L*(r+R+M)+α*(-ell-k)-(-ell-k-M-2*R)) =
          (C*Real.exp (L*(R+M)+M+2*R))*Real.exp (L*r-(α-1)*(ell+k)) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
      rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ C*Real.exp (L*(R+M)+M+2*R))]
      dsimp [K]
      ac_rfl

end Percolation.BenjaminiSchramm

end

end OAI
