import OAI.Analysis.CircleDomains.Sobolev.PrincipalScalarEnergy
import OAI.Analysis.CircleDomains.Transfer.ScalarModelPostcomposition
import OAI.Analysis.CircleDomains.Uniformization.ScalarModelCoefficients
import OAI.Analysis.CircleDomains.Topology.HolomorphicHomeomorph
import OAI.Analysis.CircleDomains.Rigidity.ConductivityDistortion
import OAI.Analysis.CircleDomains.Rigidity.ConductivityEnergy
import OAI.Analysis.CircleDomains.Rigidity.ConductivityEnergyBounds

namespace OAI

/-! The actual conductivity postcomposition stays in the retained model
class. Near maximality therefore bounds its first coefficient and both
terms of its proved global energy identity. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem complement_compact (M : CompactScalarModel G u) (hinf : OnePoint.infty ∈ G) :
    IsCompact (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ := by
  have hi : OnePoint.infty ∈ extendAtInfinity M.function '' G := ⟨_, hinf, rfl⟩
  have hK := (isCompact_finite_preimage M.image_open.isClosed_compl (not_not.mpr hi)).image
    complexPlaneCoordinates.symm.continuous
  convert hK using 1
  ext x
  constructor
  · intro hx
    exact ⟨complexPlaneCoordinates x, hx, complexPlaneCoordinates.symm_apply_apply x⟩
  · rintro ⟨z, hz, rfl⟩
    change planeSphere (complexPlaneCoordinates.symm z) ∉ extendAtInfinity M.function '' G
    simpa only [planeSphere, ContinuousLinearEquiv.apply_symm_apply, mem_preimage, mem_compl_iff] using hz

 theorem conductivity_conformal (M : CompactScalarModel G u)
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hb : (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) :
    IsConformalEquivalence φ.onePointCongr (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G)) := by
  let Ω := extendAtInfinity M.function '' G
  let F := (physicalPlaneDomain Ω)ᶜ
  have hF : IsClosed F := (isOpen_physicalPlaneDomain M.image_open).isClosed_compl
  have hh := D.conductivity_holomorphic_off φ.continuous hF n hsys
  have hC : IsConformalOn φ.onePointCongr
      (((↑) : ℂ → Sphere) '' (complexPlaneCoordinates '' F)ᶜ ∪ {OnePoint.infty}) :=
    holomorphicHomeomorph_conformal φ
      ((complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl) hh hb
  apply isConformalEquivalence_of_injOn (hC.mono ?_) M.image_open φ.onePointCongr.injective.injOn
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe z =>
    apply Or.inl
    refine ⟨z, ?_, rfl⟩
    rintro ⟨x, hx, hxz⟩
    apply hx
    change (complexPlaneCoordinates x : Sphere) ∈ Ω
    simpa only [hxz] using hp

 theorem conductivity_coefficient_le (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hscalar : CompactScalarPullback φ)
    (hFc : IsCompact (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)
    (c : ℂ) (hc : HasPrincipalCoefficient φ c) (n : ℕ) (_hn : 1 ≤ n)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) :
    c.re ≤ d := by
  let N := M.postcomposeWithScalarTransport φ
    (fun i => hscalar _ (M.scalar_continuous hu hs i) (M.scalar_compact i)
      (M.witness i) _ hFc (M.gradient_zero i)) c hc
    (M.conductivity_conformal φ D hc.bigO n hsys)
  exact M.increment_le_of_near_maximal N hbound hnear rfl

 theorem near_extremal_conductivity_energy (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (_hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))) (c : ℂ),
      HasPrincipalCoefficient φ c ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ≤ 2*Real.pi*d ∧
      (∫ x in (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) ≤ 2*Real.pi*d/((n : ℝ)-1) := by
  obtain ⟨φ, D, c, T, hT, _ht, hexp, hsys, _hh, hI, hE, hscalar⟩ :=
    exists_principal_conductivity_energy_scalar hsolver hgreen (M.complement_compact hinf) n hn
  have hc := hasPrincipalCoefficient_of_expansion hT.continuousAt hexp
  have hcd := M.conductivity_coefficient_le hu hs hbound hnear φ D hscalar (M.complement_compact hinf) c hc n (by omega) hsys
  obtain ⟨hH, hF⟩ := D.conductivity_energy_bounds hn hcd hE
  exact ⟨φ, D, c, hc, hsys, hI, hH, hF⟩

 theorem exists_near_extremal_conductivity_family
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hne : Nonempty (CompactScalarModel G u))
    {R : ℝ} (hR : 0 < R) (hsource : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G)
    {d : ℝ} (hd : 0 < d) :
    ∃ M : CompactScalarModel G u, ∀ n : ℕ, 2 ≤ n →
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))) (c : ℂ),
      HasPrincipalCoefficient φ c ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ≤ 2*Real.pi*d ∧
      (∫ x in (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) ≤ 2*Real.pi*d/((n : ℝ)-1) := by
  obtain ⟨M, hM⟩ := exists_near_maximal hne hd
  exact ⟨M, fun n hn => M.near_extremal_conductivity_energy hsolver hprincipal hgreen
    hinf hu hs (coefficientSet_bddAbove harea hR hsource) hM.le n hn⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
