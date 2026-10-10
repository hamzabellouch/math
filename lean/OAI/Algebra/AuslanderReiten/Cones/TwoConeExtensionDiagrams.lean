import OAI.Algebra.AuslanderReiten.Cones.TwoConeConnectingMaps
import OAI.Algebra.AuslanderReiten.Cones.TwoConeModuleTriangles

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

@[simp]
theorem baseStepInclusion_mk (n : ℕ) (x : D.term (n + 1)) :
    baseStepInclusion D hex n (Submodule.Quotient.mk x) = D.d n x := rfl

def middleStepInclusion (n : ℕ) :
    (BaseCokernel D (n + 3) × BaseCokernel D (n + 3)) →ₗ[R] middleTerm D n :=
  (baseStepInclusion D hex (n + 2)).prodMap (baseStepInclusion D hex (n + 2))

def singletonCoverLift (n : ℕ) : middleTerm D n →ₗ[R] SkeletonCokernel D n :=
  (LinearMap.range (skeletonD D n)).mkQ.comp (LinearMap.inr R (D.term n) (middleTerm D n))

theorem singletonCoverLift_boundary (n : ℕ) :
    (singletonCoverLift D n).comp (middleStepInclusion D hex n) =
      (bottomCokernelInclusion D n).comp (rowCokernelMap D n) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 3))).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (LinearMap.range (D.d (n + 3))).mkQ_surjective y
  change Submodule.Quotient.mk (0, (D.d (n + 2) x, D.d (n + 2) y)) =
    Submodule.Quotient.mk (D.first n x + D.second n y, (0, 0))
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨(0, (-x, -y)), ?_⟩
  simp [skeletonD, middleD, attachingRow, coneBlock_apply]
  abel

theorem singletonCoverLift_projection (n : ℕ) :
    (singletonCokernelProjection D n).comp (singletonCoverLift D n) =
      ((LinearMap.range (D.d (n + 2))).mkQ).prodMap ((LinearMap.range (D.d (n + 2))).mkQ) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

def topCoverLift (n : ℕ) : D.term (n + 4) →ₗ[R] Cokernel D n :=
  (LinearMap.range (d D n)).mkQ.comp
    (((0 : D.term (n + 4) →ₗ[R] D.term n).prod 0).prod
      ((0 : D.term (n + 4) →ₗ[R] D.term (n + 2)).prod LinearMap.id))

theorem topCoverLift_boundary (n : ℕ) :
    (topCoverLift D n).comp (baseStepInclusion D hex (n + 4)) =
      (skeletonCokernelInclusion D n).comp (-(topAttachingCokernel D n)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 5))).mkQ_surjective x
  change Submodule.Quotient.mk ((0, 0), (0, D.d (n + 4) x)) =
    skeletonCokernelInclusion D n (-Submodule.Quotient.mk
      (0, (D.second (n + 2) x, -D.first (n + 2) x)))
  rw [← Submodule.Quotient.mk_neg, skeletonCokernelInclusion_mk]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨((0, 0), (0, x)), ?_⟩
  simp [d, firstD, secondOnFirst, coneBlock_apply]

theorem topCoverLift_projection (n : ℕ) :
    (topCokernelProjection D n).comp (topCoverLift D n) = (LinearMap.range (D.d (n + 4))).mkQ := by
  apply LinearMap.ext
  intro x
  rfl

end ArExplicit.TwoCone

end

end OAI
