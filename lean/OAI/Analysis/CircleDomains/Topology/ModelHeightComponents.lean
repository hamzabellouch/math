import OAI.Analysis.CircleDomains.Topology.CompactScalarModel
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks
import OAI.Analysis.CircleDomains.Sobolev.LocalZeroGradientConstant

namespace OAI

/-! A continuous zero-gradient height is constant on every actual
complementary component of a retained deformed circle model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {v : ℂ → ℝ} (hv : Continuous v)
    (V : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    (hz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      V p = 0)
    {p q : EuclideanPlane} (hp : p ∉ physicalPlaneDomain (extendAtInfinity M.function '' G))
    (hq : planeSphere q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere p)) :
    v (complexPlaneCoordinates p) = v (complexPlaneCoordinates q) := by
  let Ω := extendAtInfinity M.function '' G
  let e := M.deformation.onePointCongr
  have he : e '' M.roundDomain = Ω := M.image_eq.symm
  have hec : e '' M.roundDomainᶜ = Ωᶜ := by rw [e.image_compl, he]
  have hp0 : e.symm (planeSphere p) ∈ M.roundDomainᶜ := by
    intro hh
    apply hp
    change planeSphere p ∈ Ω
    rw [← he]
    exact ⟨_, hh, e.apply_symm_apply _⟩
  let K := connectedComponentIn M.roundDomainᶜ (e.symm (planeSphere p))
  have hKimage : e '' K = connectedComponentIn Ωᶜ (planeSphere p) := by
    simpa only [hec, e.apply_symm_apply] using e.image_connectedComponentIn hp0
  have hpk : e.symm (planeSphere p) ∈ K := mem_connectedComponentIn hp0
  have hqk : e.symm (planeSphere q) ∈ K := by
    have hq' : planeSphere q ∈ e '' K := by rwa [hKimage]
    obtain ⟨a, ha, haq⟩ := hq'
    simpa only [← haq, e.symm_apply_apply] using ha
  rcases M.round_circle.2.2 (e.symm (planeSphere p)) hp0 with hsingle | hround
  · obtain ⟨a, ha⟩ := hsingle
    change K = {a} at ha
    have hpq : e.symm (planeSphere p) = e.symm (planeSphere q) := by
      rw [ha] at hpk hqk
      exact (mem_singleton_iff.mp hpk).trans (mem_singleton_iff.mp hqk).symm
    have hh := congrArg e hpq
    simp only [e.apply_symm_apply] at hh
    exact congrArg v (OnePoint.coe_injective hh)
  · change IsRoundClosedDisk K at hround
    have hiΩ : OnePoint.infty ∈ Ω := ⟨_, hinf, rfl⟩
    have hiround : OnePoint.infty ∈ M.roundDomain := by
      rw [← he] at hiΩ
      obtain ⟨a, ha, hai⟩ := hiΩ
      have haInf : a = OnePoint.infty := by
        apply e.injective
        exact hai
      rwa [haInf] at ha
    have hiK : OnePoint.infty ∉ K := by
      intro hh
      exact (connectedComponentIn_subset _ _ hh) hiround
    obtain ⟨c, r, hr, hK⟩ := isRoundClosedDisk_eq_euclidean hround hiK
    let E : ℂ ≃ₜ EuclideanPlane := M.deformation.trans complexPlaneCoordinates.symm.toHomeomorph
    have hE (z : ℂ) : planeSphere (E z) = e (z : Sphere) := by
      change ((complexPlaneCoordinates (complexPlaneCoordinates.symm (M.deformation z)) : ℂ) : Sphere) = _
      rw [complexPlaneCoordinates.apply_symm_apply]
      rfl
    have hsub : E '' Metric.closedBall c r ⊆ (physicalPlaneDomain Ω)ᶜ := by
      rintro a ⟨z, hz', rfl⟩
      change planeSphere (E z) ∈ Ωᶜ
      rw [hE, ← hec]
      apply mem_image_of_mem
      apply connectedComponentIn_subset M.roundDomainᶜ (e.symm (planeSphere p))
      change (z : Sphere) ∈ K
      rw [hK]
      exact ⟨z, hz', rfl⟩
    have hzE : ∀ᵐ a ∂volume.restrict (E '' Metric.closedBall c r), V a = 0 :=
      hz.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    obtain ⟨a, ha⟩ := constant_on_homeomorphic_disk (hv.comp complexPlaneCoordinates.continuous)
      V hw hLp E c hr hzE
    have hmem (t : EuclideanPlane) (ht : e.symm (planeSphere t) ∈ K) :
        t ∈ E '' Metric.closedBall c r := by
      have hback : e.symm (planeSphere t) =
          ((M.deformation.symm (complexPlaneCoordinates t) : ℂ) : Sphere) := rfl
      rw [hback, hK, OnePoint.coe_injective.mem_set_image] at ht
      refine ⟨M.deformation.symm (complexPlaneCoordinates t), ht, ?_⟩
      change complexPlaneCoordinates.symm
        (M.deformation (M.deformation.symm (complexPlaneCoordinates t))) = t
      rw [M.deformation.apply_symm_apply, complexPlaneCoordinates.symm_apply_apply]
    exact (ha p (hmem p hpk)).trans (ha q (hmem q hqk)).symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
