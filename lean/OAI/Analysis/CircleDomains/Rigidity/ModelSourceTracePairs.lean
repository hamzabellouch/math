import OAI.Analysis.CircleDomains.Transfer.ModelHeightDescent
import OAI.Analysis.CircleDomains.Rigidity.ModelHeightTracePairs
import OAI.Analysis.CircleDomains.Probability.HeightHorizontalNullPair

namespace OAI

/-! The null trace pairs on the actual target complement pull back to
all source ends through the constructed surjective projection. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem section_target_complement (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    let p := invFun M.projection (q : Sphere)
    finiteCoord p ∈ complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ∧
      planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p ∧
      M.projection p = (q : Sphere) := by
  let p := invFun M.projection (q : Sphere)
  have hpq : M.projection p = (q : Sphere) :=
    rightInverse_invFun (M.projection_surjective hsard hsch hG hconn hinf hTD) _
  have hpout : p ∉ extendAtInfinity M.function '' G := by
    rintro ⟨x, hx, he⟩
    have hh : M.projection p = x := by rw [← he, M.projection_inverse x hx]
    exact hq ((hh.symm.trans hpq) ▸ hx)
  have hpinf : p ≠ OnePoint.infty := by
    rintro h
    exact hpout (h.symm ▸ ⟨_, hinf, rfl⟩)
  have hplane : planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p := by
    simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using coe_finiteCoord hpinf
  refine ⟨?_, hplane, hpq⟩
  refine ⟨complexPlaneCoordinates.symm (finiteCoord p), ?_, complexPlaneCoordinates.apply_symm_apply _⟩
  simpa only [physicalPlaneDomain, mem_compl_iff, mem_preimage, hplane] using hpout

 theorem source_height_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) (i : Fin m) :
    let B := {q : ℂ | (q : Sphere) ∉ G}
    volume ((fun q : ℂ => (sphereFromPlaneFunction (u i) (q : Sphere),
      M.heightSection H (q : Sphere))) '' B) = 0 ∧
    volume ((fun q : ℂ => (sphereFromPlaneFunction (u i) (q : Sphere),
      M.horizontalSection (q : Sphere))) '' B) = 0 := by
  obtain ⟨hheight, hreal⟩ := M.height_trace_pairs hcoarea hinf hu hs H hHz i
  constructor
  · apply measure_mono_null (t := (fun z : ℂ =>
      (sphereFromPlaneFunction (u i) (M.projection (planeSphere (complexPlaneCoordinates.symm z))), H.height z)) ''
        (complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)) ?_ hheight
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hp, hplane, hpq⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
    refine ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, ?_⟩
    simp only [hplane, hpq, heightSection]
  · apply measure_mono_null (t := (fun z : ℂ =>
      (sphereFromPlaneFunction (u i) (M.projection (planeSphere (complexPlaneCoordinates.symm z))), z.re)) ''
        (complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)) ?_ hreal
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hp, hplane, hpq⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
    refine ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, ?_⟩
    simp only [hplane, hpq, horizontalSection]

 theorem source_height_horizontal_pair (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) :
    volume ((fun q : ℂ => (M.heightSection H (q : Sphere),
      M.horizontalSection (q : Sphere))) '' {q : ℂ | (q : Sphere) ∉ G}) = 0 := by
  let F := complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  have hF : IsCompact F := (M.complement_compact hinf).image complexPlaneCoordinates.continuous
  have hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      heightLimitGradient H.error₀ H.error₁ p = 0 := by
    rwa [Set.preimage_image_eq _ complexPlaneCoordinates.injective]
  have hh := H.horizontal_pair_null hcoarea hF hz
  apply measure_mono_null (t := (fun z => (H.height z, z.re)) '' F) ?_ hh
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hp, _, _⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
  exact ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, rfl⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
