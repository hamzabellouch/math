import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModelData
import OAI.Analysis.CircleDomains.Uniformization.ScalarModelCoefficients

namespace OAI

/-! The constructed circle model belongs to the coefficient-extremal class. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 namespace CompactScalarCircleModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_compact (M : CompactScalarCircleModel G u)
    (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    HasCompactSupport (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) := by
  have hp : M.projection OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
  have ht := M.projection_continuous.tendsto OnePoint.infty
  rw [hp] at ht
  have hz₀ : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction (u i) p = 0 := by
    let K := complexPlaneCoordinates '' tsupport (u i)
    have hK : IsCompact K := (hs i).isCompact.image complexPlaneCoordinates.continuous
    have hN : (((↑) : ℂ → Sphere) '' K)ᶜ ∈ 𝓝 (OnePoint.infty : Sphere) :=
      (OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩).mem_nhds
        OnePoint.infty_notMem_image_coe
    filter_upwards [hN] with p hp
    cases p using OnePoint.rec with
    | infty => simp [sphereFromPlaneFunction]
    | coe z =>
      rw [sphereFromPlaneFunction_coe]
      apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hp ⟨z, ⟨complexPlaneCoordinates.symm z, hz,
        complexPlaneCoordinates.apply_symm_apply z⟩, rfl⟩
  have hz := ht.eventually hz₀
  have hC : HasCompactSupport (fun z : ℂ => sphereFromPlaneFunction (u i) (M.projection z)) := by
    rw [hasCompactSupport_iff_eventuallyEq]
    exact OnePoint.tendsto_coe_infty.eventually hz
  exact hC.comp_homeomorph complexPlaneCoordinates.toHomeomorph

 def toCompactScalarModel (M : CompactScalarCircleModel G u)
    (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i))
    (b : ℂ) (hb : HasPrincipalCoefficient M.function b) : CompactScalarModel G u where
  function := M.function
  coefficient := b
  coefficient_limit := hb
  conformal := M.conformal
  roundDomain := extendAtInfinity M.function '' G
  round_circle := M.circle
  deformation := Homeomorph.refl ℂ
  image_eq := by
    have he : ((Homeomorph.refl ℂ).onePointCongr : Sphere → Sphere) = id := by
      funext p
      cases p using OnePoint.rec <;> rfl
    rw [he, image_id]
  projection := M.projection
  projection_continuous := M.projection_continuous
  projection_inverse := M.projection_inverse
  projection_outside := M.projection_outside
  projection_component := M.projection_component
  witness := M.witness
  gradient_zero := M.gradient_zero
  scalar_compact := M.scalar_compact hinf hs

 end CompactScalarCircleModel
 theorem CompactScalarCircleModel.exists_coefficient
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (M : CompactScalarCircleModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ b : ℂ, HasPrincipalCoefficient M.function b := by
  have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ G := by
    have ht : Tendsto (fun z : ℂ => (z : Sphere)) (cobounded ℂ) (𝓝 OnePoint.infty) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (OnePoint.tendsto_coe_infty : Tendsto (fun z : ℂ => (z : Sphere)) _ _)
    exact ht.eventually (hG.mem_nhds hinf)
  apply exists_principal_coefficient
  · exact hm.mono fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)
  · simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.normalized.2

 theorem nonempty_compactScalarModel_of_circle
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i))
    (hM : Nonempty (CompactScalarCircleModel G u)) : Nonempty (CompactScalarModel G u) := by
  obtain ⟨M⟩ := hM
  obtain ⟨b, hb⟩ := M.exists_coefficient hG hinf
  exact ⟨M.toCompactScalarModel hinf hs b hb⟩

end CircleDomainRigidity

end

end OAI
