import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModel

namespace OAI

/-! The empty-dust case uses the identity and the original Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 def compactScalarCircleModel_identity {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) univ) :
    CompactScalarCircleModel univ u := by
  have hf : extendAtInfinity (id : ℂ → ℂ) = (id : Sphere → Sphere) := by
    funext p
    cases p using OnePoint.rec <;> rfl
  refine {
    function := id
    normalized := ?_
    conformal := ?_
    circle := ?_
    projection := id
    projection_continuous := continuous_id
    projection_inverse := ?_
    projection_outside := ?_
    projection_component := ?_
    witness := fun i => (H i).congr_ae (Eventually.of_forall fun x => ?_)
    gradient_zero := ?_ }
  · rw [hf]
    refine ⟨rfl, ?_⟩
    simpa only [id_eq, finiteCoord_coe, sub_self] using
      (Asymptotics.isBigO_zero (E' := ℂ) (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ))
  · simpa only [hf, image_id] using isConformalEquivalence_id (univ : Set Sphere)
  · simpa only [hf, image_id] using isCircleDomain_univ
  · intro p _
    rw [hf]
    rfl
  · intro p hp
    exact (hp (by rw [hf, image_id]; trivial)).elim
  · intro p hp
    exact (hp (by rw [hf, image_id]; trivial)).elim
  · simp only [id_eq, planeSphere, sphereFromPlaneFunction_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  · intro i j
    exact Eventually.of_forall fun x hx => (hx (by rw [hf, image_id]; trivial)).elim

end CircleDomainRigidity

end

end OAI
