import OAI.Analysis.CircleDomains.Topology.CompactScalarModel

namespace OAI

/-! Postcomposition of actual scalar models. The scalar witnesses and their
zero complementary gradients follow from the published chain rule and
null-set preservation. The topological data are transported explicitly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem extendAtInfinity_postcompose (φ : ℂ ≃ₜ ℂ) (f : ℂ → ℂ) :
    extendAtInfinity (φ ∘ f) = φ.onePointCongr ∘ extendAtInfinity f := by
  funext p
  cases p using OnePoint.rec <;> rfl

 theorem physicalPlaneDomain_homeomorph_image (φ : ℂ ≃ₜ ℂ) (Ω : Set Sphere) :
    physicalPlaneDomain (φ.onePointCongr '' Ω) =
      physicalHomeomorph φ '' physicalPlaneDomain Ω := by
  ext x
  rw [φ.onePointCongr.image_eq_preimage_symm,
    (physicalHomeomorph φ).image_eq_preimage_symm]
  change φ.onePointCongr.symm (planeSphere x) ∈ Ω ↔
    planeSphere ((physicalHomeomorph φ).symm x) ∈ Ω
  rw [physicalHomeomorph_symm, planeSphere_physicalHomeomorph]
  rfl

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def postcomposeWithScalarTransport (M : CompactScalarModel G u)
    (φ : ℂ ≃ₜ ℂ)
    (htransport : ∀ i, ∃ V : DeGiorgi.MemW1pWitness 2
      ((fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) ∘
        physicalHomeomorph φ.symm) univ,
      ∀ j, ∀ᵐ x ∂volume,
        x ∈ physicalHomeomorph φ '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ →
          V.weakGrad x j=0)
    (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) : CompactScalarModel G u := by
  let f := φ ∘ M.function
  let Ω := extendAtInfinity M.function '' G
  let e := φ.onePointCongr
  have hf : extendAtInfinity f = e ∘ extendAtInfinity M.function :=
    extendAtInfinity_postcompose φ M.function
  have him : extendAtInfinity f '' G = e '' Ω := by rw [hf, image_comp]
  let P : Sphere → Sphere := M.projection ∘ e.symm
  have hscalar (i : Fin m) :
      (fun x => sphereFromPlaneFunction (u i) (P (planeSphere x))) =
        (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) ∘
          physicalHomeomorph φ.symm := by
    funext x
    rw [comp_apply, planeSphere_physicalHomeomorph]
    rfl
  have hphys : (physicalPlaneDomain (extendAtInfinity f '' G))ᶜ =
      physicalHomeomorph φ '' (physicalPlaneDomain Ω)ᶜ := by
    rw [him, physicalPlaneDomain_homeomorph_image, (physicalHomeomorph φ).image_compl]
  choose V hV using htransport
  let hV' (i : Fin m) : DeGiorgi.MemW1pWitness 2
      (fun x => sphereFromPlaneFunction (u i) (P (planeSphere x))) univ :=
    (V i).congr_ae (Eventually.of_forall (fun x => congrFun (hscalar i).symm x))
  refine {
    function := f
    coefficient := M.coefficient+c
    coefficient_limit := M.coefficient_limit.comp hc
    conformal := ?_
    roundDomain := M.roundDomain
    round_circle := M.round_circle
    deformation := M.deformation.trans φ
    image_eq := ?_
    projection := P
    projection_continuous := M.projection_continuous.comp e.symm.continuous
    projection_inverse := ?_
    projection_outside := ?_
    projection_component := ?_
    witness := hV'
    gradient_zero := ?_
    scalar_compact := ?_ }
  · rw [hf, image_comp]
    exact M.conformal.trans hconf
  · rw [him]
    change e '' (extendAtInfinity M.function '' G) = _
    rw [M.image_eq, ← image_comp]
    congr 1
    funext p
    cases p using OnePoint.rec <;> rfl
  · intro p hp
    change M.projection (e.symm (extendAtInfinity f p)) = p
    rw [hf, comp_apply, e.symm_apply_apply]
    exact M.projection_inverse p hp
  · intro p hp
    apply M.projection_outside
    intro hh
    apply hp
    rw [him]
    exact ⟨e.symm p, hh, e.apply_symm_apply p⟩
  · intro p hp q hq
    have hpold : e.symm p ∉ Ω := by
      intro hh
      apply hp
      rw [him]
      exact ⟨e.symm p, hh, e.apply_symm_apply p⟩
    have hback : e.symm '' (extendAtInfinity f '' G)ᶜ = Ωᶜ := by
      rw [him, ← e.image_compl, image_image]
      simp only [e.symm_apply_apply, image_id']
    have hqback := e.symm.continuous.continuousOn.image_connectedComponentIn_subset hp
      (mem_image_of_mem e.symm hq)
    rw [hback] at hqback
    exact M.projection_component (e.symm p) hpold (e.symm q) hqback
  · intro i j
    have he := hV i j
    rw [← hphys] at he
    exact he
  · intro i
    rw [hscalar]
    exact (M.scalar_compact i).comp_homeomorph (physicalHomeomorph φ.symm)

 def postcompose (M : CompactScalarModel G u) (hqc : PlaneQuasiconformalCalculus)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (φ : ℂ ≃ₜ ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) : CompactScalarModel G u := by
  exact M.postcomposeWithScalarTransport φ
    (fun i => quasiconformal_compact_zero_gradient hqc φ D hd
      (M.scalar_continuous hu hs i) (M.scalar_compact i) (M.witness i)
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ (M.gradient_zero i))
    c hc hconf

 @[simp] theorem postcompose_coefficient (M : CompactScalarModel G u)
    (hqc : PlaneQuasiconformalCalculus)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hd : D.HasBoundedDistortion) (c : ℂ) (hc : HasPrincipalCoefficient φ c)
    (hconf : IsConformalEquivalence φ.onePointCongr
      (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G))) :
    (M.postcompose hqc hu hs φ D hd c hc hconf).coefficient = M.coefficient+c := rfl

 end CompactScalarModel
end CircleDomainRigidity

end

end OAI
