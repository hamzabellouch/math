import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationReaction

namespace OAI

/-! # Quadratic deviation from the actual linearized evolution

On a fixed finite slab, a bounded nonlinear perturbation differs from its
linearized evolution by the quadratic Taylor term and the profile defect.
This is the quantitative comparison part of the manuscript's `nl:step`.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingPerturbation_linear_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ)
    (q g v : C(Icc (0 : ℝ) T, FourierL2)) (v₀ : FourierL2)
    (hv : v = expandingPicard a b k L T ha hk hL hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ v) :
    ∀ t : Icc (0 : ℝ) T, v t =
      expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q
              (expandingPerturbationSource a k L T ha ha1 hk hL m q g v)) v) := by
  have he : expandingReactionHistory T hT
      (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v =
      expandingReactionHistory T hT
        (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q
          (expandingPerturbationSource a k L T ha ha1 hk hL m q g v)) v := by
    funext τ
    exact expandingPerturbationReaction_split a k L T ha ha1 hk hL m q g v
      (projIcc 0 T hT τ)
  intro t
  have h := congrArg (fun w : C(Icc (0 : ℝ) T, FourierL2) => w t) hv
  change v t = expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
    expandingDuhamel a b k L ha hk hL t
      (expandingReactionHistory T hT
        (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v) at h
  rwa [he] at h

/-- The comparison constant is independent of the starting radius.  The
perturbation is an actual nonlinear mild solution, not an abstract error. -/
theorem exists_expandingNonlinearStep_quadratic_error (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
      (q g v w : C(Icc (0 : ℝ) T, FourierL2)) (v₀ : FourierL2) (d G : ℝ),
      0 ≤ d → d ≤ 1 → 0 ≤ G → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      (∀ t, ‖v t‖ ≤ d) →
      v = expandingPicard a b k L T ha hk hL hT
        (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ v →
      (∀ t : Icc (0 : ℝ) T, w t =
        expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory T hT
              (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0) w)) →
      dist v w ≤ Real.exp ((K + 1) * T) * (C * d ^ 2 + G) := by
  obtain ⟨K, hK, hresponse⟩ := exists_expandingProfile_response_bound a b k ha ha1 hk m R hR
  obtain ⟨C, hC, hsource⟩ := exists_expandingPerturbationSource_bound a k ha ha1 hk m R hR
  refine ⟨K, C, hK, hC, ?_⟩
  intro L T hL hT q g v w v₀ d G hd hd1 hG hq hg hv hvsol hwsol
  exact hresponse L T hL hT q
    (expandingPerturbationSource a k L T ha ha1 hk hL m q g v) v₀ (C * d ^ 2 + G)
    (by positivity) hq (hsource L T hL q g v d G hd hd1 hG hq hg hv) v w
    (expandingPerturbation_linear_mild a b k L T ha ha1 hk hL hT m q g v v₀ hvsol) hwsol

end DefocusingNLS

end OAI
