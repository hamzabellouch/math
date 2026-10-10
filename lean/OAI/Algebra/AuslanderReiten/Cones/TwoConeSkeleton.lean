import OAI.Algebra.AuslanderReiten.Cones.TwoConeProjective
import OAI.Algebra.AuslanderReiten.Cones.CokernelLinearCongr
import OAI.Algebra.AuslanderReiten.Cones.CokernelProduct

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

abbrev middleTerm (n : ℕ) := D.term (n + 2) × D.term (n + 2)

abbrev skeletonTerm (n : ℕ) : ModuleCat.{u} R := ModuleCat.of R (D.term n × middleTerm D n)

def middleD (n : ℕ) : middleTerm D (n + 1) →ₗ[R] middleTerm D n :=
  (D.d (n + 2)).prodMap (D.d (n + 2))

def attachingRow (n : ℕ) : middleTerm D (n + 1) →ₗ[R] D.term n :=
  (D.first n).coprod (D.second n)

def skeletonD (n : ℕ) : skeletonTerm D (n + 1) →ₗ[R] skeletonTerm D n :=
  coneBlock (D.d n) (middleD D n) (attachingRow D n)

theorem middleD_square (n : ℕ) : (middleD D n).comp (middleD D (n + 1)) = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  exact Prod.ext (DFunLike.congr_fun (D.square (n + 2)) x)
    (DFunLike.congr_fun (D.square (n + 2)) y)

theorem attachingRow_comm (n : ℕ) :
    (D.d n).comp (attachingRow D (n + 1)) = (attachingRow D n).comp (middleD D (n + 1)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change D.d n (D.first (n + 1) x + D.second (n + 1) y) =
    D.first n (D.d (n + 3) x) + D.second n (D.d (n + 3) y)
  rw [map_add]
  exact congrArg₂ (· + ·) (DFunLike.congr_fun (D.first_comm n) x)
    (DFunLike.congr_fun (D.second_comm n) y)

theorem skeletonD_square (n : ℕ) : (skeletonD D n).comp (skeletonD D (n + 1)) = 0 :=
  coneBlock_comp_zero _ _ _ _ _ _ (D.square n) (middleD_square D n) (attachingRow_comm D n)

def skeletonComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (skeletonTerm D) (fun n => ModuleCat.ofHom (skeletonD D n))
    (fun n => ModuleCat.hom_ext (skeletonD_square D n))

theorem middleD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (middleD D (n + 1)) (middleD D n) := by
  rintro ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (hex (n + 2) x).mp (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (hex (n + 2) y).mp (congrArg Prod.snd h)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact Prod.ext ((hex (n + 2) x).mpr ⟨a, congrArg Prod.fst h⟩)
      ((hex (n + 2) y).mpr ⟨b, congrArg Prod.snd h⟩)

theorem skeletonD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (skeletonD D (n + 1)) (skeletonD D n) :=
  coneBlock_exact _ _ _ _ _ _ (hex n) (middleD_exact D hex n) (attachingRow_comm D n)

def topAttaching (n : ℕ) : D.term (n + 5) →ₗ[R] skeletonTerm D n :=
  (0 : D.term (n + 5) →ₗ[R] D.term n).prod
    ((D.second (n + 2)).prod (-(D.first (n + 2))))

@[simp]
theorem topAttaching_apply (n : ℕ) (x : D.term (n + 5)) :
    topAttaching D n x = (0, (D.second (n + 2) x, -D.first (n + 2) x)) := rfl

theorem topAttaching_comm (n : ℕ) :
    (skeletonD D n).comp (topAttaching D (n + 1)) =
      (topAttaching D n).comp (-(D.d (n + 5))) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change D.d n 0 + (D.first n (D.second (n + 3) x) +
      D.second n (-D.first (n + 3) x)) = 0
    rw [map_zero, zero_add, map_neg]
    rw [show D.first n (D.second (n + 3) x) = D.second n (D.first (n + 3) x)
      from DFunLike.congr_fun (D.comparisons_comm n) x, add_neg_cancel]
  · apply Prod.ext
    · change -D.d (n + 2) (D.second (n + 3) x) = D.second (n + 2) (-D.d (n + 5) x)
      rw [map_neg]
      exact congrArg Neg.neg (DFunLike.congr_fun (D.second_comm (n + 2)) x)
    · change -D.d (n + 2) (-D.first (n + 3) x) = -D.first (n + 2) (-D.d (n + 5) x)
      rw [map_neg, map_neg, neg_neg, neg_neg]
      exact DFunLike.congr_fun (D.first_comm (n + 2)) x

def skeletonCoordinates (n : ℕ) : term D n ≃ₗ[R] (skeletonTerm D n × D.term (n + 4)) where
  toFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  invFun x := ((x.1.1, x.1.2.1), (x.1.2.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem skeletonCoordinates_d (n : ℕ) :
    (skeletonCoordinates D n).toLinearMap.comp (d D n) =
      (coneBlock (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)).comp
        (skeletonCoordinates D (n + 1)).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simp [skeletonCoordinates, d, firstD, secondOnFirst, coneBlock_apply, skeletonD,
    middleD, attachingRow, topAttaching, add_assoc]
  abel

abbrev SkeletonCokernel (n : ℕ) := skeletonTerm D n ⧸ LinearMap.range (skeletonD D n)

def skeletonCokernelCoordinates (n : ℕ) : Cokernel D n ≃ₗ[R]
    ConeCokernel.Middle (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n) :=
  cokernelLinearCongr _ _ (skeletonCoordinates D (n + 1)) (skeletonCoordinates D n)
    (skeletonCoordinates_d D n)

def negativeTopCokernelEquiv (n : ℕ) :
    ConeCokernel.Right (-(D.d (n + 4))) ≃ₗ[R] BaseCokernel D (n + 4) :=
  Submodule.quotEquivOfEq _ _ (by simp)

def skeletonCokernelInclusion (n : ℕ) : SkeletonCokernel D n →ₗ[R] Cokernel D n :=
  (skeletonCokernelCoordinates D n).symm.toLinearMap.comp
    (ConeCokernel.inclusion (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n))

def topCokernelProjection (n : ℕ) : Cokernel D n →ₗ[R] BaseCokernel D (n + 4) :=
  (negativeTopCokernelEquiv D n).toLinearMap.comp
    ((ConeCokernel.projection (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)).comp
      (skeletonCokernelCoordinates D n).toLinearMap)

@[simp]
theorem topCokernelProjection_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2))
    (e : D.term (n + 4)) :
    topCokernelProjection D n (Submodule.Quotient.mk ((a, b), (c, e))) =
      Submodule.Quotient.mk e := rfl

def middleCokernelEquiv (n : ℕ) : ConeCokernel.Right (middleD D n) ≃ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  cokernelProductEquiv (D.d (n + 2)) (D.d (n + 2))

def bottomCokernelInclusion (n : ℕ) : BaseCokernel D n →ₗ[R] SkeletonCokernel D n :=
  ConeCokernel.inclusion (D.d n) (middleD D n) (attachingRow D n)

def singletonCokernelProjection (n : ℕ) : SkeletonCokernel D n →ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  (middleCokernelEquiv D n).toLinearMap.comp
    (ConeCokernel.projection (D.d n) (middleD D n) (attachingRow D n))

@[simp]
theorem bottomCokernelInclusion_mk (n : ℕ) (a : D.term n) :
    bottomCokernelInclusion D n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (a, (0, 0)) := rfl

@[simp]
theorem singletonCokernelProjection_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2)) :
    singletonCokernelProjection D n (Submodule.Quotient.mk (a, (b, c))) =
      (Submodule.Quotient.mk b, Submodule.Quotient.mk c) := rfl

@[simp]
theorem skeletonCokernelInclusion_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2)) :
    skeletonCokernelInclusion D n (Submodule.Quotient.mk (a, (b, c))) =
      Submodule.Quotient.mk ((a, b), (c, 0)) := rfl

theorem bottomCokernelInclusion_injective
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Injective (bottomCokernelInclusion D n) :=
  ConeCokernel.inclusion_injective _ _ _ (middleD D (n + 1)) (attachingRow D (n + 1))
    (middleD_exact D hex n) (attachingRow_comm D n)

theorem singletonCokernelProjection_surjective (n : ℕ) :
    Function.Surjective (singletonCokernelProjection D n) :=
  (middleCokernelEquiv D n).surjective.comp (ConeCokernel.projection_surjective _ _ _)

theorem skeletonCokernel_exact (n : ℕ) :
    Function.Exact (bottomCokernelInclusion D n) (singletonCokernelProjection D n) := by
  intro x
  change middleCokernelEquiv D n
    (ConeCokernel.projection (D.d n) (middleD D n) (attachingRow D n) x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact ConeCokernel.exact _ _ _ x

theorem negativeD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (-(D.d (n + 1))) (-(D.d n)) := by
  intro x
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hex n x).mp (neg_eq_zero.mp h)
    exact ⟨-y, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    apply neg_eq_zero.mpr
    exact (hex n x).mpr ⟨-y, by simpa using hy⟩

theorem skeletonCokernelInclusion_injective
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Injective (skeletonCokernelInclusion D n) :=
  (skeletonCokernelCoordinates D n).symm.injective.comp
    (ConeCokernel.inclusion_injective _ _ _ (-(D.d (n + 5))) (topAttaching D (n + 1))
      (negativeD_exact D hex (n + 4)) (topAttaching_comm D n))

theorem topCokernelProjection_surjective (n : ℕ) :
    Function.Surjective (topCokernelProjection D n) :=
  (negativeTopCokernelEquiv D n).surjective.comp
    ((ConeCokernel.projection_surjective _ _ _).comp
      (skeletonCokernelCoordinates D n).surjective)

theorem topCokernel_exact (n : ℕ) :
    Function.Exact (skeletonCokernelInclusion D n) (topCokernelProjection D n) := by
  intro x
  change negativeTopCokernelEquiv D n
    (ConeCokernel.projection (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)
      (skeletonCokernelCoordinates D n x)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (ConeCokernel.exact (skeletonD D n) (-(D.d (n + 4)))
      (topAttaching D n) (skeletonCokernelCoordinates D n x)).mp h
    refine ⟨y, ?_⟩
    change (skeletonCokernelCoordinates D n).symm
      (ConeCokernel.inclusion (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n) y) = x
    rw [hy, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy⟩
    apply (ConeCokernel.exact _ _ _ _).mpr
    refine ⟨y, ?_⟩
    rw [← hy]
    exact ((skeletonCokernelCoordinates D n).apply_symm_apply _).symm

end ArExplicit.TwoCone

end

end OAI
