import OAI.Algebra.AuslanderReiten.Cones.TwoCone

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)
variable (g : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+2))
variable (b : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+4))

def highLift (n : ℕ) : Q (n+3) →ₗ[R] term D n :=
  (0 : Q (n+3) →ₗ[R] firstTerm D n).prod ((g n).prod (b n))

@[simp] theorem highLift_apply (n : ℕ) (x : Q (n+3)) :
    highLift D Q g b n x = ((0,0),(g n x,b n x)) := rfl

theorem highLift_comm
    (hb : ∀ n, (D.d (n+4)).comp (b (n+1)) = (b n).comp (δ (n+3)))
    (hg : ∀ n, -(D.d (n+2)).comp (g (n+1)) -
      (D.first (n+2)).comp (b (n+1)) = (g n).comp (δ (n+3)))
    (hsecondg : ∀ n, (D.second n).comp (g (n+1)) = 0)
    (hsecondb : ∀ n, (D.second (n+2)).comp (b (n+1)) = 0) (n : ℕ) :
    (d D n).comp (highLift D Q g b (n+1)) =
      (highLift D Q g b n).comp (δ (n+3)) := by
  apply LinearMap.ext
  intro x
  change d D n ((0,0),(g (n+1) x,b (n+1) x)) =
    ((0,0),(g n (δ (n+3) x),b n (δ (n+3) x)))
  rw [d_apply]
  apply Prod.ext
  · apply Prod.ext
    · simpa only [map_zero, zero_add, LinearMap.comp_apply, LinearMap.zero_apply] using DFunLike.congr_fun (hsecondg n) x
    · simpa only [map_zero, neg_zero, zero_add, LinearMap.comp_apply, LinearMap.zero_apply] using DFunLike.congr_fun (hsecondb n) x
  · exact Prod.ext (DFunLike.congr_fun (hg n) x) (DFunLike.congr_fun (hb n) x)

abbrev FourthCokernel := Q 4 ⧸ LinearMap.range (δ 4)

def tailMap (φ₄ : Q 4 →ₗ[R] term D 1) (φ₅ : Q 5 →ₗ[R] term D 2)
    (hφ : (d D 1).comp φ₅ = φ₄.comp (δ 4)) :
    FourthCokernel Q δ →ₗ[R] C₁ D :=
  (LinearMap.range (δ 4)).liftQ (((LinearMap.range (d D 1)).mkQ).comp φ₄) (by
    rintro x ⟨y,rfl⟩
    change (LinearMap.range (d D 1)).mkQ (φ₄ (δ 4 y)) = 0
    rw [← show d D 1 (φ₅ y) = φ₄ (δ 4 y) from DFunLike.congr_fun hφ y]
    exact DFunLike.congr_fun (LinearMap.range_mkQ_comp (d D 1)) (φ₅ y))

@[simp] theorem tailMap_mk (φ₄ : Q 4 →ₗ[R] term D 1) (φ₅ : Q 5 →ₗ[R] term D 2)
    (hφ : (d D 1).comp φ₅ = φ₄.comp (δ 4)) (x : Q 4) :
    tailMap D Q δ φ₄ φ₅ hφ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ₄ x) := rfl

end ArExplicit.TwoCone

end

end OAI
