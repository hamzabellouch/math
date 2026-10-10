import OAI.Analysis.CircleDomains.Selection.RegularAssignedStokes
import OAI.Analysis.CircleDomains.Rigidity.MaskedStokesApplication

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hσ : Injective σ) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ s, 0 ≤ r s)
    (hd : Pairwise (Disjoint on fun s => closedBall (c s) (r s)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ s, closedBall (c s) (r s))ᶜ)
    (htarget : ∀ s, ((↑) : ℂ → Sphere) '' closedBall (c s) (r s) ⊆
      connectedComponentIn T.model.domainᶜ (a.point s))
    (m : ℕ) (κ : Fin m → T.indices) (hκ : Injective κ) (b : Fin m)
    (hsing : (κ b : S) = (C l).singular) (hmask : ∀ j, σ (κ j) ∈ (C l).mask)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (W : Set ℂ) (hW : IsOpen W)
    (hsub : closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆ W)
    (hsmooth : SmoothCircleOn (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere))) W)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j))))) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
            (T.model.inverse (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ (C l).singular},
          ((C l).upper s - (C l).lower s) ^ 2) + ε) := by
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  have hne (j : Fin m) (hj : j ≠ b) : σ (κ j) ≠ σ (C l).singular := by
    intro he
    apply hj
    apply hκ
    apply Subtype.ext
    exact (hσ he).trans hsing.symm
  choose V hV hboundary hcont hproj hosc using
    (fun j : {j : Fin m // j ≠ b} => T.nonsingular_terminal_lift l (κ j) (hmask j) (hne j j.property))
  let V' (j : Fin m) := if h : j ≠ b then V ⟨j, h⟩ else univ
  let A (j : Fin m) := Metric.diam
    (T.terminal_branch (κ j) l '' frontier (realJordanInterior (T.terminals.H (κ j))))
  let P := {s : T.indices // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular}
  let label : {j : Fin m // j ≠ b} → P := fun j => ⟨κ j, hmask j, hne j j.property⟩
  have hlabel : Injective label := by
    intro i j he
    apply Subtype.ext
    exact hκ (congrArg Subtype.val he)
  have hexc : Real.sqrt (∑ j : {j : Fin m // j ≠ b},
      max (A j - ((C l).upper (κ j) - (C l).lower (κ j))) 0 ^ 2) ≤ ε := by
    have h := finite_label_band_norm_le label hlabel
      (fun s : P => max (Metric.diam (T.terminal_branch s l ''
        frontier (realJordanInterior (T.terminals.H s))) -
          ((C l).upper s - (C l).lower s)) 0)
      (hasSum_fintype _).summable
    exact h.trans (T.terminal_excess l).le
  have hb := assigned_model_stokes_nonsingular_bound_regular hgreen a T.model.equivalence
    c r hr hd hext htarget m κ hκ b H γ hγ hin W hW hsub
    (sphereRealFunction (T.model.functions l)) hsmooth hL hbounded henergy V'
    (fun j => sphereRealFunction (T.terminal_branch (κ j) l))
    (fun j hj => by simpa only [V', dite_eq_left hj] using hV ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hboundary ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hcont ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hproj ⟨j, hj⟩)
    A (fun j hj => hosc ⟨j, hj⟩) (fun s : T.indices => (s : S)) Subtype.val_injective
    (fun s => (C l).upper s - (C l).lower s) (C l).width_summable (C l).width_nonneg hexc
  rw [hsing] at hb
  exact hb

 theorem MaskedCoordinateStage.source_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
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
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ)
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
  have hb := T.stokes_bound_regular hgreen hσ l a c r hr hd hext htarget m κ hκ b hsing hmask H γ hγ hin
    (Complex.equivRealProdCLM ⁻¹' T.targetMask l) hW hregion hu hL hbounded hi'
  have hle := setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi)
    (ae_of_all _ (fun z => sq_nonneg ‖circleFDeriv u z‖)) (ae_of_all _ hsub)
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle.trans he.le))
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

 theorem StokesCollarGeometry.source_stokes_bound_regular
    (hgreen : UnorientedFiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    {T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀} {l : Fin n}
    {s : T.indices} {H : ℂ ≃ₜ ℂ}
    {a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain}
    (D : StokesCollarGeometry T l s H a)
    (hG : IsOpen G) (hπ : Continuous π) (hσ : Injective σ)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p)
    (hsing : (s : S) = (C l).singular)
    (γ : ℝ → ℂ) (hγ : RegularJordanParametrization D.target γ)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior D.target ⊆ closedBall 0 L) :
    |circleFormIntegral (fun z => infDist z (closedBall (D.center s) (D.radius s)))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        ((∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
          fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε) +
      2 * Real.pi * L *
        (Real.sqrt (∑' t : {t : S // t ≠ (C l).singular},
          ((C l).upper t - (C l).lower t) ^ 2) + ε) := by
  have hb := T.source_stokes_bound_regular hgreen hG hπ hσ hmetric l a
    D.center D.radius D.radius_nonneg D.disjoint D.exterior
    (fun i => D.disks i ▸ Subset.rfl) D.count D.label D.injective D.base
    (by rw [D.distinguished]; exact hsing) D.mask D.target γ hγ D.inside D.region hL hbounded
  simpa only [D.distinguished] using hb


end CircleDomainRigidity.FiniteTransfer

end

end OAI
