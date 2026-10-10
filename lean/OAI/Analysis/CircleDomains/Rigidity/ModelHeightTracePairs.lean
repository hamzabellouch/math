import OAI.Analysis.CircleDomains.Probability.HorizontalNullPair
import OAI.Analysis.CircleDomains.Selection.ControlledHeight

namespace OAI

/-! The two null trace-pair conclusions for every retained scalar of an
actual compact model and its constructed conductivity height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_trace_pairs (M : CompactScalarModel G u)
    (hcoarea : PlanarSobolevCoarea) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) (i : Fin m) :
    let F := complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
    let U := fun z : ℂ => sphereFromPlaneFunction (u i)
      (M.projection (planeSphere (complexPlaneCoordinates.symm z)))
    volume ((fun z => (U z, H.height z)) '' F) = 0 ∧
      volume ((fun z => (U z, z.re)) '' F) = 0 := by
  let F₀ := (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  let F := complexPlaneCoordinates '' F₀
  let U := fun p => sphereFromPlaneFunction (u i) (M.projection (planeSphere p))
  have hF₀ : IsCompact F₀ := M.complement_compact hinf
  have hF : IsCompact F := hF₀.image complexPlaneCoordinates.continuous
  have hpre : complexPlaneCoordinates ⁻¹' F = F₀ :=
    Set.preimage_image_eq F₀ complexPlaneCoordinates.injective
  obtain ⟨S, hS⟩ := hF.isBounded.subset_ball 0
  let T := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFQ : F ⊆ interior (closedBall (0 : ℂ) T) := by
    rw [interior_closedBall _ hT.ne']
    exact hS.trans (ball_subset_ball (le_max_left _ _))
  have hUc : Continuous U := M.scalar_continuous hu hs i
  have hWz (j : Fin 2) : ∀ᵐ p ∂volume.restrict F₀, (M.witness i).weakGrad p j = 0 := by
    apply (ae_restrict_iff' hF₀.measurableSet).mpr
    exact M.gradient_zero i j
  have hWzero : ∀ᵐ p ∂volume.restrict F₀, (M.witness i).weakGrad p = 0 := by
    filter_upwards [hWz 0, hWz 1] with p hp0 hp1
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext j
    fin_cases j <;> assumption
  constructor
  · apply sobolev_height_pair_null_image hcoarea H.approximants H.height.continuous H.height_limit
      H.weak_gradient (fun r j => (heightLimitWitness H.error₀ H.error₁
        (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient r).weakGrad_component_memLp j)
      hF (isCompact_closedBall 0 T) hFQ _ hUc (M.witness i)
    simpa only [hpre] using hHz
  · apply sobolev_horizontal_pair_null_image hcoarea hF (isCompact_closedBall 0 T) hFQ hUc (M.witness i)
    simpa only [hpre] using hWzero

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
