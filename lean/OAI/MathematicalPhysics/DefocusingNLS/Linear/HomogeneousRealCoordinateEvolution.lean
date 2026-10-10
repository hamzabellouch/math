import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealStableCoordinates

namespace OAI

/-! # Exact evolution of the real contour coordinates -/

open Set
open scoped NNReal

namespace DefocusingNLS

theorem homogeneousLinearizedTrajectory_initial (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q u : HomogeneousY a k) :
    homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q u ⟨0, le_rfl, hT⟩ = u := by
  rw [homogeneousLinearizedTrajectory_eq]
  simp only [homogeneousDuhamel, intervalIntegral.integral_same, add_zero,
    homogeneousFreeOperator_zero]

theorem homogeneousStableCoordinates_step (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) P)
    (t : ℝ≥0) (u : HomogeneousY a k) :
    homogeneousStableCoordinates a k ha ha1 hk P
      (homogeneousLinearizedStep a b k ha ha1 hk m q t u) =
      projectionSemigroupRestriction (homogeneousComplexLinearizedStep a b k ha ha1 hk m q)
        P hcomm t (homogeneousStableCoordinates a k ha ha1 hk P u) := by
  apply Subtype.ext
  change P (homogeneousComplexEmbed a k ha ha1 hk
    (homogeneousLinearizedStep a b k ha ha1 hk m q t u)) =
    homogeneousComplexLinearizedStep a b k ha ha1 hk m q t
      (P (homogeneousComplexEmbed a k ha ha1 hk u))
  rw [← homogeneousComplexification_embed]
  exact (congrArg (fun A : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
      (HomogeneousY a k × HomogeneousY a k) => A (homogeneousComplexEmbed a k ha ha1 hk u))
    (hcomm t).eq).symm

theorem homogeneousStableCoordinates_slab (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T) (m : ℕ) (q : HomogeneousY a k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) P)
    (t : Icc (0 : ℝ) T) (u : HomogeneousY a k) :
    homogeneousStableCoordinates a k ha ha1 hk P
      (homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q u t) =
      projectionSemigroupRestriction (homogeneousComplexLinearizedStep a b k ha ha1 hk m q)
        P hcomm ⟨t, t.2.1⟩ (homogeneousStableCoordinates a k ha ha1 hk P u) := by
  have h := homogeneousStableCoordinates_step a b k ha ha1 hk m q P hcomm ⟨t, t.2.1⟩ u
  rwa [homogeneousLinearizedStep_eq_slab a b k ha ha1 hk m q T hT ⟨t, t.2.1⟩ t.2.2] at h

end DefocusingNLS

end OAI
