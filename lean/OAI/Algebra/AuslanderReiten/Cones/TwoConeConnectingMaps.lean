import OAI.Algebra.AuslanderReiten.Cones.TwoConeSkeleton

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

def firstCokernelMap (n : ℕ) : BaseCokernel D (n + 3) →ₗ[R] BaseCokernel D n :=
  (LinearMap.range (D.d (n + 3))).liftQ
    ((LinearMap.range (D.d n)).mkQ.comp (D.first n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨D.first (n + 1) y, DFunLike.congr_fun (D.first_comm n) y⟩)

def secondCokernelMap (n : ℕ) : BaseCokernel D (n + 3) →ₗ[R] BaseCokernel D n :=
  (LinearMap.range (D.d (n + 3))).liftQ
    ((LinearMap.range (D.d n)).mkQ.comp (D.second n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨D.second (n + 1) y, DFunLike.congr_fun (D.second_comm n) y⟩)

@[simp]
theorem firstCokernelMap_mk (n : ℕ) (x : D.term (n + 3)) :
    firstCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.first n x) := rfl

@[simp]
theorem secondCokernelMap_mk (n : ℕ) (x : D.term (n + 3)) :
    secondCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.second n x) := rfl

def rowCokernelMap (n : ℕ) : (BaseCokernel D (n + 3) × BaseCokernel D (n + 3)) →ₗ[R]
    BaseCokernel D n :=
  (firstCokernelMap D n).coprod (secondCokernelMap D n)

def columnCokernelMap (n : ℕ) : BaseCokernel D (n + 5) →ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  (secondCokernelMap D (n + 2)).prod (-(firstCokernelMap D (n + 2)))

def topAttachingCokernel (n : ℕ) : BaseCokernel D (n + 5) →ₗ[R] SkeletonCokernel D n :=
  (LinearMap.range (D.d (n + 5))).liftQ
    ((LinearMap.range (skeletonD D n)).mkQ.comp (topAttaching D n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨-topAttaching D (n + 1) y, ?_⟩
      have h := DFunLike.congr_fun (topAttaching_comm D n) y
      change skeletonD D n (topAttaching D (n + 1) y) = topAttaching D n (-D.d (n + 5) y) at h
      rw [map_neg] at h
      rw [map_neg, h, neg_neg])

@[simp]
theorem topAttachingCokernel_mk (n : ℕ) (x : D.term (n + 5)) :
    topAttachingCokernel D n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (0, (D.second (n + 2) x, -D.first (n + 2) x)) := rfl

theorem topAttachingCokernel_adjacent (n : ℕ) :
    (singletonCokernelProjection D n).comp (topAttachingCokernel D n) = columnCokernelMap D n := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 5))).mkQ_surjective x
  change (Submodule.Quotient.mk (D.second (n + 2) x),
      Submodule.Quotient.mk (-D.first (n + 2) x)) =
    (Submodule.Quotient.mk (D.second (n + 2) x), -Submodule.Quotient.mk (D.first (n + 2) x))
  rw [Submodule.Quotient.mk_neg]

end ArExplicit.TwoCone

end

end OAI
