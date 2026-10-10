import OAI.Analysis.CircleDomains.Rigidity.MaskedStageStokes
import OAI.Analysis.CircleDomains.Rigidity.MaskedStageEnergy

namespace OAI

/-! The actual finite Stokes inequality with its energy charged to the
original masked coordinate. Neither target integrability nor a target
energy budget is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.source_stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hπ : Continuous π) (hσ : Injective σ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ s, 0 ≤ r s)
    (hd : Pairwise (Disjoint on fun s => closedBall (c s) (r s)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ s, closedBall (c s) (r s))ᶜ)
    (htarget : ∀ s, ((↑) : ℂ → Sphere) '' closedBall (c s) (r s) ⊆
      connectedComponentIn T.model.domainᶜ (a.point s))
    (m : ℕ) (κ : Fin m → T.indices) (hκ : Injective κ) (b : Fin m)
    (hsing : (κ b : S) = (C l).singular) (hmask : ∀ j, σ (κ j) ∈ (C l).mask)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (hregion : closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
      Complex.equivRealProdCLM ⁻¹' T.targetMask l)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ (C l).singular},
          ((C l).upper s - (C l).lower s) ^ 2) + ε) := by
  let u := fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))
  have hueq : u = (T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM := by
    funext z
    simp only [u, sphereRealFunction, sphereRealMap, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have hs := T.model.transported l
  have hW : IsOpen (Complex.equivRealProdCLM ⁻¹' T.targetMask l) :=
    hs.1.preimage Complex.equivRealProdCLM.continuous
  have hu : SmoothCircleOn u (Complex.equivRealProdCLM ⁻¹' T.targetMask l) := by
    rw [hueq]
    intro z hz a ha
    exact (hs.2.1 _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  obtain ⟨hi, he⟩ := T.complex_energy_lt hG hπ hmetric l
  rw [← hueq] at hi he
  have hsub : jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆
      Complex.equivRealProdCLM ⁻¹' T.targetMask l :=
    fun z hz => hregion ⟨subset_closure hz.1, hz.2⟩
  have hi' := hi.mono_measure (Measure.restrict_mono_set volume hsub)
  have hb := T.stokes_bound hgreen hσ l a c r hr hd hext htarget m κ hκ b hsing hmask H γ hγ hin
    (Complex.equivRealProdCLM ⁻¹' T.targetMask l) hW hregion hu hL hbounded hi'
  have hle := setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi)
    (ae_of_all _ (fun z => sq_nonneg ‖circleFDeriv u z‖)) (ae_of_all _ hsub)
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle.trans he.le))
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
