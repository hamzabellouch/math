import OAI.Analysis.CircleDomains.Modulus.FilledFirstArrivalBarrier
import OAI.Analysis.CircleDomains.Sobolev.SmoothedBarrierPlateaus
import OAI.Analysis.CircleDomains.Sobolev.SmoothedBarrierCompatibility
import OAI.Analysis.CircleDomains.Probability.LocalizedDensityNorm
import OAI.Analysis.CircleDomains.Sobolev.LocalizedRealGradientNorm

namespace OAI

/-! The actual compatible smooth barrier from the first-arrival obstruction.
The norm outside the penalty region depends only on the original density;
the perturbation is used solely to obtain the plateaus and path inequality. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_compatible_smooth_first_arrival_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (E EStar : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior E)
    (hinfE : π OnePoint.infty ∈ interior E)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hN : ∀n labels, (Measure.pi (fun _ : Fin (n + 1) =>
      (volume : Measure UnitAddCircle))) (N n labels) = 0)
    (F : Set Sphere) (hF : MeasurableSet F) (hFB : F ⊆ d.dust)
    (hmF : ∀x ∈ F, m x = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃(k l : ℕ) (O : Set Sphere) (Q : PhysicalRealCoordinate d π),
      k < l ∧ IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      (∀x ∈ EStar, Q.quotient x = 0) ∧
      (∀x ∈ closure (D l).region ∩ d.quotientDomain, Q.quotient x = 1) ∧
      (∀s ∈ d.dust, ENNReal.ofReal (limsup Q.quotient (𝓝[d.quotientDomain] s) -
        liminf Q.quotient (𝓝[d.quotientDomain] s)) ≤ 4 * m s) ∧
      (∀i : Fin 2, eLpNorm (fun y => (fderiv ℝ Q.physical y)
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain \
            (fun y : ℝ × ℝ => π (Complex.equivRealProdCLM.symm y : Sphere)) ⁻¹' O)) ≤
        ε + ENNReal.ofReal (4 * (9 * C)) *
          (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)) ∧
      ∀n labels, (volume.prod (Measure.pi (fun _ : Fin (n + 1) =>
        (volume : Measure UnitAddCircle))))
        (freeComponentFailure F (circleBandGraph d.quotientDomain Q.quotient)
          (fun i => circleBandGraph d.quotientDomain (previous i).quotient) labels) = 0 := by
  obtain ⟨k, O, g₁, u, hO, hOU, hEO, hfO, hg₁, _, hagree, henergy₁,
    hu, huE, huD, hpath, hband⟩ := exists_filled_first_arrival_barrier_potential
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hdisj hBU
      hdense hinfty hbad ν N E hE hEU p hpDust hp D hnest hshrink hED f hf W₁ W₂
      hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
  have hDk := (D k).isOpen_region hπ hclosed hsurj hr
  obtain ⟨j, hj⟩ := hshrink ((D k).region \ {π OnePoint.infty})
    ((hDk.sdiff isClosed_singleton).mem_nhds ⟨(D k).point_mem_region hsurj hp, hp⟩)
  let l := max j (k + 1)
  have hl : closure (D l).region ⊆ (D k).region \ {π OnePoint.infty} :=
    hj l (le_max_left _ _)
  let T : Set (ℝ × ℝ) := FiniteTransfer.realChartDomain d.physicalDomain \
    (fun y : ℝ × ℝ => π (Complex.equivRealProdCLM.symm y : Sphere)) ⁻¹' O
  let S := euclideanPlaneCoordinates ⁻¹' T
  have hT : MeasurableSet T :=
    (FiniteTransfer.isOpen_realChartDomain hG).measurableSet.diff
      ((hO.preimage (hπ.comp (OnePoint.continuous_coe.comp
        Complex.equivRealProdCLM.symm.continuous))).measurableSet)
  have hS : S ⊆ physicalPlaneDomain d.physicalDomain := fun _ hx => hx.1
  obtain ⟨v, Q, hv, hQ, hzero, hone, hcontract, hnorm⟩ :=
    smooth_barrier_with_anchor_and_terminal d hG hdisj π hπ he hinf hinfty hB ⟨p, hpDust⟩
      E EStar (closure (D l).region) (D k).region hEU hEStar hEStarE hinfE
      isClosed_closure (fun x hx => (hl hx).1) hDk
      (fun hx => (hl hx).2 rfl) ν N u hu huE (fun x hx => huD x (subset_closure hx))
      g₁ hg₁ henergy₁ m hm hpath C hC hderiv S hS hε
  refine ⟨k, l, O, Q, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _),
    hO, hOU, hEO, hfO, hzero, hone, ?_, ?_, ?_⟩
  · intro s hs
    apply le_trans (ENNReal.ofReal_le_ofReal (sub_le_sub (hcontract s hs
      (by rw [hdense.closure_eq]; trivial)).2 (hcontract s hs
      (by rw [hdense.closure_eq]; trivial)).1)) (hband s hs)
  · intro i
    have hlocal := (hnorm i).1.mono_measure (Measure.restrict_mono_set volume hS)
    rw [physical_coordinate_partial_eLpNorm_on d hG π he v hv Q hQ hT
      (fun _ hx => hx.1) i hlocal]
    refine (hnorm i).2.trans (add_le_add le_rfl ?_)
    exact localized_perturbed_density_eLpNorm_le π O S
      (hT.preimage euclideanPlaneCoordinates.continuous.measurable) (fun _ hx => hx.2)
      g g₁ hg henergy hagree (4 * (9 * C)) (by positivity)
  · intro n labels
    apply smoothed_barrier_compatibility_with_physical_coordinates hcoarea hLusin d hU hG hdisj
      π hπ hsurj hfiber (fun y => (he y).symm) hB.isCompact hTD
      (by rintro _ ⟨y, hy, rfl⟩; exact hbad y hy) hBU hdisj
      (by rw [hdense.closure_eq]; exact subset_univ _) hF hFB harcs previous hlevels
      g₁ hg₁ henergy₁ m hm₂ hmF hweights hpoint ν N u hu hpath hband Q
      (fun s hs => hcontract s hs (by rw [hdense.closure_eq]; trivial)) n labels (hN n labels)

end CircleDomainRigidity

end

end OAI
