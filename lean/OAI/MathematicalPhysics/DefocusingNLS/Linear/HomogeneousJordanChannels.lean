import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInhomogeneousChannels

namespace OAI

/-! # The exact PDE source associated with a finite Jordan chain

The relation G w = λ w + v gives the physical source v in both circular
channels. All contour vectors are in the actual generator domain.
-/

open Set
open scoped Laplacian ZeroAtInfty NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- The coupled eigenvalue equation with an explicitly represented source. -/
def IsClassicalLinearizedSourcePair (a b : ℝ) (m : ℕ)
    (q f g F G : E → ℂ) (lam : ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ ∀ x : E,
    (lam * f x + F x = Complex.I * Δ f x - (1 / 2 : ℂ) * fderiv ℝ f x x +
      (-(a : ℂ) + Complex.I * (b : ℂ)) * f x - Complex.I *
        ((((m + 1 : ℕ) : ℂ) * q x ^ m * star (q x) ^ m) * f x +
          ((m : ℂ) * q x ^ (m + 1) * star (q x) ^ (m - 1)) * g x)) ∧
    (lam * g x + G x = -Complex.I * Δ g x - (1 / 2 : ℂ) * fderiv ℝ g x x +
      (-(a : ℂ) - Complex.I * (b : ℂ)) * g x + Complex.I *
        (star (((m + 1 : ℕ) : ℂ) * q x ^ m * star (q x) ^ m) * g x +
          star ((m : ℂ) * q x ^ (m + 1) * star (q x) ^ (m - 1)) * f x))

theorem homogeneous_contour_jordan_channels (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (Q : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
      (HomogeneousY a k × HomogeneousY a k))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) Q)
    (hfin : FiniteDimensional ℂ Q.range) (G : Q.range →L[ℂ] Q.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) Q hcomm t =
        NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (w v : Q.range) (he : G w = lam • w + v) :
    let P := fun f : HomogeneousY a k =>
      fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
    IsClassicalLinearizedSourcePair a b m (P q)
      (P (w : HomogeneousY a k × HomogeneousY a k).1)
      (P (w : HomogeneousY a k × HomogeneousY a k).2)
      (P (v : HomogeneousY a k × HomogeneousY a k).1)
      (P (v : HomogeneousY a k × HomogeneousY a k).2) lam := by
  dsimp only
  have hd := projectionSemigroup_generator_domain
    (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) Q hcomm hfin G hG w
  have hp := homogeneous_generator_classical_channels a b k ha ha1 hk m q
    (w : HomogeneousY a k × HomogeneousY a k) (G w : HomogeneousY a k × HomogeneousY a k) hd
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro x
  have hval : (G w : HomogeneousY a k × HomogeneousY a k) =
      lam • (w : HomogeneousY a k × HomogeneousY a k) +
        (v : HomogeneousY a k × HomogeneousY a k) := by
    exact congrArg Subtype.val he
  have hx := hp.2.2 x
  rw [hval] at hx
  change homogeneousPhysicalCLM a k ha ha1 hk
      (lam • (w : HomogeneousY a k × HomogeneousY a k).1 +
        (v : HomogeneousY a k × HomogeneousY a k).1) x = _ ∧
    homogeneousPhysicalCLM a k ha ha1 hk
      (lam • (w : HomogeneousY a k × HomogeneousY a k).2 +
        (v : HomogeneousY a k × HomogeneousY a k).2) x = _ at hx
  simpa only [map_add, map_smul, ZeroAtInftyContinuousMap.add_apply,
    ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul] using hx

end DefocusingNLS

end OAI
