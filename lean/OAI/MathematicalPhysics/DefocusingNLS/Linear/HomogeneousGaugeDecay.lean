import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedQuotient

namespace OAI

/-! # Energy decay of the actual logarithmic gauge channels -/

open Set Filter Topology Asymptotics MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem homogeneousGauge_energy_decay
    (Q F G f g : ℝ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hQ : ∀ r, Q r ≠ 0)
    (hpair : ∀ r, (Q r * (f r + Complex.I * g r),
      star (Q r) * (f r - Complex.I * g r)) = (F r, G r))
    (hU : (fun r => F r / Q r) =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)))
    (hdU : deriv (fun r => F r / Q r) =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ)))
    (hV : (fun r => G r / star (Q r)) =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)))
    (hdV : deriv (fun r => G r / star (Q r)) =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) :
    (f =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv f =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) ∧
    (g =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv g =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) := by
  let U := fun r => F r / Q r
  let V := fun r => G r / star (Q r)
  have hUE : U = fun r => f r + Complex.I * g r := by
    funext r
    dsimp only [U]
    have hp : Q r * (f r + Complex.I * g r) = F r := congrArg Prod.fst (hpair r)
    rw [← hp]
    apply (div_eq_iff (hQ r)).2
    ring
  have hVE : V = fun r => f r - Complex.I * g r := by
    funext r
    dsimp only [V]
    have hp : star (Q r) * (f r - Complex.I * g r) = G r := congrArg Prod.snd (hpair r)
    rw [← hp]
    apply (div_eq_iff (star_ne_zero.mpr (hQ r))).2
    ring
  have hUd : deriv U = fun r => deriv f r + Complex.I * deriv g r := by
    rw [hUE]
    funext r
    exact ((hf r).hasDerivAt.add ((hg r).hasDerivAt.const_mul Complex.I)).deriv
  have hVd : deriv V = fun r => deriv f r - Complex.I * deriv g r := by
    rw [hVE]
    funext r
    exact ((hf r).hasDerivAt.sub ((hg r).hasDerivAt.const_mul Complex.I)).deriv
  have hfe : f = fun r => (1 / 2 : ℂ) * (U r + V r) := by
    rw [hUE, hVE]
    funext r
    ring
  have hge : g = fun r => (1 / (2 * Complex.I) : ℂ) * (U r - V r) := by
    rw [hUE, hVE]
    funext r
    field_simp [Complex.I_ne_zero]; ring
  have hdfe : deriv f = fun r => (1 / 2 : ℂ) * (deriv U r + deriv V r) := by
    rw [hUd, hVd]
    funext r
    ring
  have hdge : deriv g = fun r => (1 / (2 * Complex.I) : ℂ) * (deriv U r - deriv V r) := by
    rw [hUd, hVd]
    funext r
    field_simp [Complex.I_ne_zero]; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hfe]
    exact (hU.add hV).const_mul_left _
  · rw [hdfe]
    exact (hdU.add hdV).const_mul_left _
  · rw [hge]
    exact (hU.sub hV).const_mul_left _
  · rw [hdge]
    exact (hdU.sub hdV).const_mul_left _

theorem homogeneous_matched_gauge_decay
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hlam : 4 ≤ lam.re)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) eta lam F G)
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(F r, G r)‖ ≤ M)
    (hL2F : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N F r‖ ^ 2) (Ioi 0))
    (hL2G : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N G r‖ ^ 2) (Ioi 0))
    (Yp Ym : ℂ → ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpair : ∀ r, (radialMatchedEvenProfile n z r * (f r + Complex.I * g r),
      star (radialMatchedEvenProfile n z r) * (f r - Complex.I * g r)) = (F r, G r)) :
    (∀ L : ℂ →L[ℝ] ℝ, HasRadialEnergyDecay (fun r => L (f r))) ∧
      (∀ L : ℂ →L[ℝ] ℝ, HasRadialEnergyDecay (fun r => L (g r))) := by
  obtain ⟨c, R₀, _, hstate⟩ := homogeneous_matched_pair_canonical_tail n z hX hz eta N hN
    lam (by linarith) F G hF hG he hbounded hL2F hL2G Yp Ym hYp hYm
  obtain ⟨hU, hV⟩ := homogeneous_matched_quotient_decay n z hX eta lam hlam
    F G Yp Ym hYp hYm c R₀ hstate
  obtain ⟨hfd, hgd⟩ := homogeneousGauge_energy_decay (radialMatchedEvenProfile n z) F G f g
    (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))
    (radialMatchedEvenProfile_ne_zero n z hX) hpair hU.1 hU.2 hV.1 hV.2
  exact ⟨fun L => homogeneousComplexEnergyDecay_real f hfd.1 hfd.2
      (Eventually.of_forall (hf.differentiable (by norm_num))) L,
    fun L => homogeneousComplexEnergyDecay_real g hgd.1 hgd.2
      (Eventually.of_forall (hg.differentiable (by norm_num))) L⟩

end DefocusingNLS

end OAI
