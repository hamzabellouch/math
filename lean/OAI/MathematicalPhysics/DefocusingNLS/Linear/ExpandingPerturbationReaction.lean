import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileResponse

namespace OAI

/-! # Exact nonlinear perturbation and quadratic forcing

The perturbation of the actual odd-power equation splits into its profile
linearization and its Taylor remainder.  The estimates are uniform in the
expanding torus radius and are the nonlinear ingredients of `nl:step`.
-/

open Set

namespace DefocusingNLS

noncomputable def expandingPerturbationReaction (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q g : C(Icc (0 : ℝ) T, FourierL2)) :
    C((Icc (0 : ℝ) T) × FourierL2, FourierL2) where
  toFun p := (-Complex.I) •
    (expandingOddPower a k (expandingRadiusCurve L T hL p.1).1 ha ha1 hk
        (expandingRadiusCurve L T hL p.1).2 m (q p.1 + p.2) -
      expandingOddPower a k (expandingRadiusCurve L T hL p.1).1 ha ha1 hk
        (expandingRadiusCurve L T hL p.1).2 m (q p.1)) - g p.1
  continuous_toFun := by
    have hl := (expandingRadiusCurve L T hL).continuous.comp
      (continuous_fst : Continuous (Prod.fst : (Icc (0 : ℝ) T) × FourierL2 → _))
    have hq := q.continuous.comp
      (continuous_fst : Continuous (Prod.fst : (Icc (0 : ℝ) T) × FourierL2 → _))
    exact (((continuous_expandingOddPower_scale a k ha ha1 hk m).comp
      (hl.prodMk (hq.add continuous_snd))).sub
      ((continuous_expandingOddPower_scale a k ha ha1 hk m).comp (hl.prodMk hq))).const_smul
        (-Complex.I) |>.sub (g.continuous.comp continuous_fst)

noncomputable def expandingPerturbationSource (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q g v : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, v t) -
    expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0 (t, v t)
  continuous_toFun :=
    ((expandingPerturbationReaction a k L T ha ha1 hk hL m q g).continuous.comp
      (continuous_id.prodMk v.continuous)).sub
      ((expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0).continuous.comp
        (continuous_id.prodMk v.continuous))

theorem expandingPerturbationSource_apply (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q g v : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    expandingPerturbationSource a k L T ha ha1 hk hL m q g v t =
      (-Complex.I) • expandingNonlinearRemainder a k (expandingRadiusCurve L T hL t).1
        ha ha1 hk (expandingRadiusCurve L T hL t).2 m (q t) (v t) - g t := by
  change (-Complex.I) • (_ - _) - g t - ((-Complex.I) • _ + 0) = _
  simp only [expandingNonlinearRemainder, smul_sub, add_zero]
  abel

theorem expandingPerturbationReaction_split (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q g v : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, v t) =
      expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q
        (expandingPerturbationSource a k L T ha ha1 hk hL m q g v) (t, v t) := by
  let A : FourierL2 := expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, v t)
  let D : FourierL2 := (-Complex.I) •
    fderiv ℝ (expandingOddPower a k (expandingRadiusCurve L T hL t).1 ha ha1 hk
      (expandingRadiusCurve L T hL t).2 m) (q t) (v t)
  change A = D + (A - (D + 0))
  abel

theorem exists_expandingPerturbationSource_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L)
      (q g v : C(Icc (0 : ℝ) T, FourierL2)) (d G : ℝ),
      0 ≤ d → d ≤ 1 → 0 ≤ G → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      (∀ t, ‖v t‖ ≤ d) → ∀ t,
      ‖expandingPerturbationSource a k L T ha ha1 hk hL m q g v t‖ ≤ C * d ^ 2 + G := by
  obtain ⟨C, hC, hb⟩ := exists_expandingNonlinearRemainder_quadratic a k ha ha1 hk m R hR
  refine ⟨C, hC, ?_⟩
  intro L T hL q g v d G hd hd1 hG hq hg hv t
  rw [expandingPerturbationSource_apply]
  calc
    _ ≤ ‖(-Complex.I) • expandingNonlinearRemainder a k
        (expandingRadiusCurve L T hL t).1 ha ha1 hk (expandingRadiusCurve L T hL t).2
        m (q t) (v t)‖ + ‖g t‖ := norm_sub_le _ _
    _ = ‖expandingNonlinearRemainder a k (expandingRadiusCurve L T hL t).1 ha ha1 hk
        (expandingRadiusCurve L T hL t).2 m (q t) (v t)‖ + ‖g t‖ := by
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ C * ‖v t‖ ^ 2 + G := add_le_add
      (hb _ (expandingRadiusCurve L T hL t).2 _ _ (hq t) ((hv t).trans hd1)) (hg t)
    _ ≤ C * d ^ 2 + G := add_le_add (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hv t) 2) hC) le_rfl

theorem exists_expandingPerturbationSource_lipschitz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L)
      (q g v w : C(Icc (0 : ℝ) T, FourierL2)) (d : ℝ),
      0 ≤ d → d ≤ 1 → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖v t‖ ≤ d) →
      (∀ t, ‖w t‖ ≤ d) → ∀ t,
      ‖expandingPerturbationSource a k L T ha ha1 hk hL m q g v t -
        expandingPerturbationSource a k L T ha ha1 hk hL m q g w t‖ ≤
        (2 * C * d) * dist v w := by
  obtain ⟨C, hC, hb⟩ := exists_expandingNonlinearRemainder_lipschitz a k ha ha1 hk m R hR
  refine ⟨C, hC, ?_⟩
  intro L T hL q g v w d hd hd1 hq hv hw t
  rw [expandingPerturbationSource_apply, expandingPerturbationSource_apply,
    sub_sub_sub_cancel_right, ← smul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ C * (‖v t‖ + ‖w t‖) * ‖v t - w t‖ :=
      hb _ (expandingRadiusCurve L T hL t).2 _ _ _ (hq t) ((hv t).trans hd1) ((hw t).trans hd1)
    _ ≤ (2 * C * d) * dist v w := by
      apply mul_le_mul
      · nlinarith [mul_le_mul_of_nonneg_left (add_le_add (hv t) (hw t)) hC]
      · simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := v) (g := w) t
      · exact norm_nonneg _
      · positivity

end DefocusingNLS

end OAI
