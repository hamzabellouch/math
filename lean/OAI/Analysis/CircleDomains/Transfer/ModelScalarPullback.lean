import OAI.Analysis.CircleDomains.Transfer.ModelScalarDescent
import OAI.Analysis.CircleDomains.Sobolev.SobolevConformalTransport

namespace OAI

/-! A compact global Sobolev target scalar constant on the omitted
components descends to a compact continuous source scalar, with the
conformally transported Sobolev witness on the source domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem planeInverseTransport_extendAtInfinity (f : ℂ → ℂ)
    (v : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    planeInverseTransport (extendAtInfinity f) v x =
      sphereFromPlaneFunction v (extendAtInfinity f (planeSphere x)) := by
  simp only [planeInverseTransport, Function.comp_apply, sphereRealMap,
    planeSphere, extendAtInfinity_coe, finiteCoord_coe, sphereFromPlaneFunction_coe]
  rfl

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_scalar_pullback (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hvs : HasCompactSupport v)
    (V : DeGiorgi.MemW1pWitness 2 v univ)
    (hc : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p,
        sphereFromPlaneFunction v p = sphereFromPlaneFunction v q) :
    let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
    Continuous w ∧ HasCompactSupport w ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 w (physicalPlaneDomain G),
        (∫ x in physicalPlaneDomain G, W.weakGrad x 0^2+W.weakGrad x 1^2) ≤
          ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
            V.weakGrad x 0^2+V.weakGrad x 1^2 := by
  obtain ⟨hcont, hsupp, hvalue⟩ := M.compact_scalar_descent hsard hsch hG hconn hinf hTD hv hvs hc
  let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
  have hw : Continuous w := hcont.comp continuous_planeSphere
  have hws : HasCompactSupport w := hsupp.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  obtain ⟨hfc, hmap, fi, hfic, hfimap, hl, hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hi : OnePoint.infty ∈ extendAtInfinity M.function '' G := ⟨_, hinf, rfl⟩
  have hL : MemLp w 2 (volume.restrict (physicalPlaneDomain G)) :=
    (hw.memLp_of_hasCompactSupport hws).restrict _
  obtain ⟨W, hW⟩ := sobolev_conformal_transport heq M.image_open hG hi hfi hfic hv hvs V
    (v := w) (fun x hx => by
      rw [planeInverseTransport_extendAtInfinity]
      exact hvalue (planeSphere x) hx) hL
  exact ⟨hw, hws, W, hW⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
