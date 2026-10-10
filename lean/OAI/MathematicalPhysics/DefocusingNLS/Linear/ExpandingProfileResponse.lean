import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # Uniform finite-slab response to forcing in the actual linearized equation

An exponential time weight bounds the response on an arbitrary fixed slab.
The constants are independent of the initial torus radius and use the
actual odd-power derivative along the given bounded profile.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingMild_finiteSlab_residual_bound (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ t : Icc (0 : ℝ) T, u t =
      expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u))
    (hv : ∀ t : Icc (0 : ℝ) T,
      Real.exp (-(K + 1) * t) *
        ‖v t - expandingPicard a b k L T ha hk hL hT F u₀ v t‖ ≤ ε) :
    dist u v ≤ Real.exp ((K + 1) * T) * ((K + 1) * ε) := by
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  let P := expandingBieleckiPicard a b k L T η ha hk hL hT F u₀
  let u' := expandingTimeWeight T (-η) u
  let v' := expandingTimeWeight T (-η) v
  have hKη : K / η < 1 := (div_lt_one hη).2 (by dsimp [η]; linarith)
  have hP : ContractingWith ⟨K / η, div_nonneg hK hη.le⟩ P :=
    ⟨hKη, LipschitzWith.of_dist_le_mul
      (expandingBieleckiPicard_dist_le a b k L T η ha hk hL hT hη F u₀ K hK hF)⟩
  have huP : Function.IsFixedPt P u' :=
    expandingBielecki_isFixedPt a b k L T η ha hk hL hT F u₀ u hu
  have hvP : dist v' (P v') ≤ ε := by
    apply (ContinuousMap.dist_le hε).2
    intro t
    change dist (Real.exp (-η * t) • v t)
      (Real.exp (-η * t) •
        expandingPicard a b k L T ha hk hL hT F u₀
          (expandingTimeWeight T η (expandingTimeWeight T (-η) v)) t) ≤ ε
    rw [expandingTimeWeight_cancel, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hv t
  have hd := (hP.dist_le_of_fixedPoint v' huP).trans
    (div_le_div_of_nonneg_right hvP (sub_nonneg.mpr hKη.le))
  change dist v' u' ≤ ε / (1 - K / η) at hd
  have hden : 1 - K / η = 1 / η := by
    apply (eq_div_iff hη.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hη.ne', one_mul]
    dsimp [η]
    ring
  rw [hden, div_div_eq_mul_div, div_one] at hd
  have hout := expandingTimeWeight_dist_le T η hη.le u' v'
  have heq : dist u v ≤ Real.exp (η * T) * dist u' v' := by
    simpa only [u', v', expandingTimeWeight_cancel] using hout
  calc
    dist u v ≤ Real.exp (η * T) * dist u' v' := heq
    _ ≤ Real.exp (η * T) * (ε * η) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hd) (Real.exp_pos _).le
    _ = _ := by dsimp [η]; ring

/-- Bounded forcing in the actual profile linearization has a response bound
on every finite slab, uniformly in the starting radius. -/
theorem exists_expandingProfile_response_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
      (q g : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2)
      (G : ℝ), 0 ≤ G → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      ∀ u v : C(Icc (0 : ℝ) T, FourierL2),
      (∀ t : Icc (0 : ℝ) T, u t =
        expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory T hT
              (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g) u)) →
      (∀ t : Icc (0 : ℝ) T, v t =
        expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory T hT
              (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0) v)) →
      dist u v ≤ Real.exp ((K + 1) * T) * G := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingProfileReaction_lipschitz a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT q g u₀ G hG hq hg u v hu hv
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  let F := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g
  let F₀ := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0
  let r₀ := expandingReactionHistory T hT F₀ v
  let r := fun τ : ℝ => g (projIcc 0 T hT τ)
  have hr₀ : Continuous r₀ := continuous_expandingReactionHistory T hT F₀ v
  have hr : Continuous r := g.continuous.comp continuous_projIcc
  have hsplit : expandingReactionHistory T hT F v = fun τ => r₀ τ + r τ := by
    funext τ
    change (-Complex.I • _ + g (projIcc 0 T hT τ)) =
      (-Complex.I • _ + 0) + g (projIcc 0 T hT τ)
    rw [add_zero]
  have hdef (t : Icc (0 : ℝ) T) :
      expandingPicard a b k L T ha hk hL hT F u₀ v t =
        v t + expandingDuhamel a b k L ha hk hL t r := by
    change expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F v) = _
    rw [hsplit, expandingDuhamel_add a b k L ha hk hL t r₀ r
      hr₀.continuousOn hr.continuousOn, ← add_assoc, ← hv t]
  have hdef_bound (t : Icc (0 : ℝ) T) :
      Real.exp (-(K + 1) * t) *
        ‖v t - expandingPicard a b k L T ha hk hL hT F u₀ v t‖ ≤ G / η := by
    rw [hdef]
    rw [show v t - (v t + expandingDuhamel a b k L ha hk hL t r) =
      -expandingDuhamel a b k L ha hk hL t r by abel, norm_neg]
    have hb := expandingDuhamel_weighted_norm_le a b k L η t G ha hk hL hη t.2.1 hG r
      (fun τ hτ => (hg _).trans (le_mul_of_one_le_right hG
        (Real.one_le_exp_iff.mpr (mul_nonneg hη.le hτ.1))))
    exact hb
  have hb := expandingMild_finiteSlab_residual_bound a b k L T ha hk hL hT F u₀ K (G / η)
    hK (div_nonneg hG hη.le) (hbound T (expandingRadiusCurve L T hL) q g hq)
    u v hu hdef_bound
  have he : (K + 1) * (G / η) = G := by
    change η * (G / η) = G
    exact mul_div_cancel₀ G hη.ne'
  rwa [he] at hb

end DefocusingNLS

end OAI
