import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearityTransport
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildContraction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLinearization

namespace OAI

/-! # The actual nonautonomous linearized potential

A continuous profile and a continuous expanding radius give the potential
`-i D(|u|^(2m)u)|q(t)`.  Its short-time construction uses the uniform exact
`Y_L` derivative bounds already proved, not a separately assumed potential.
-/

namespace DefocusingNLS

/-- The actual real-linearized odd-power reaction along a moving profile. -/
noncomputable def expandingProfileReaction (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (l : C(Set.Icc (0 : ℝ) T, {L : ℝ // 1 ≤ L}))
    (q g : C(Set.Icc (0 : ℝ) T, FourierL2)) :
    C((Set.Icc (0 : ℝ) T) × FourierL2, FourierL2) where
  toFun p := -Complex.I •
    fderiv ℝ (expandingOddPower a k (l p.1).1 ha ha1 hk (l p.1).2 m) (q p.1) p.2 + g p.1
  continuous_toFun := by
    have hp : Continuous (fun p : (Set.Icc (0 : ℝ) T) × FourierL2 =>
        (l p.1, (q p.1, p.2))) :=
      (l.continuous.comp continuous_fst).prodMk
        ((q.continuous.comp continuous_fst).prodMk continuous_snd)
    exact (((continuous_expandingLinearization_scale a k ha ha1 hk m).comp hp).const_smul
      (-Complex.I : ℂ)).add (g.continuous.comp continuous_fst)

/-- One Lipschitz bound applies to every starting scale and every bounded profile. -/
theorem exists_expandingProfileReaction_lipschitz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ)
      (l : C(Set.Icc (0 : ℝ) T, {L : ℝ // 1 ≤ L}))
      (q g : C(Set.Icc (0 : ℝ) T, FourierL2)),
      (∀ t, ‖q t‖ ≤ R) → ∀ t x y,
      ‖expandingProfileReaction a k T ha ha1 hk m l q g (t, x) -
        expandingProfileReaction a k T ha ha1 hk m l q g (t, y)‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingOddPower_two_jet_bound a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro T l q g hq t x y
  have hD : ‖fderiv ℝ (expandingOddPower a k (l t).1 ha ha1 hk (l t).2 m) (q t)‖ ≤ K := by
    rw [← norm_iteratedFDeriv_one]
    exact hbound (l t).1 (l t).2 (q t) (hq t) 1 (by decide)
  change ‖(-Complex.I •
      fderiv ℝ (expandingOddPower a k (l t).1 ha ha1 hk (l t).2 m) (q t) x + g t) -
    (-Complex.I •
      fderiv ℝ (expandingOddPower a k (l t).1 ha ha1 hk (l t).2 m) (q t) y + g t)‖ ≤ _
  rw [add_sub_add_right_eq_sub, ← smul_sub, ← map_sub, norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact ((fderiv ℝ (expandingOddPower a k (l t).1 ha ha1 hk (l t).2 m) (q t)).le_opNorm
    (x - y)).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))

/-- The radius follows exactly the manuscript's moving family `L exp(t/2)`. -/
noncomputable def expandingRadiusCurve (L T : ℝ) (hL : 1 ≤ L) :
    C(Set.Icc (0 : ℝ) T, {M : ℝ // 1 ≤ M}) where
  toFun t := ⟨expandingRadius L t, hL.trans (expandingRadius_ge L t hL t.2.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_subtype_val.div_const 2))

/-- The reaction is exactly the scalar linearized Schrödinger potential at each point. -/
theorem expandingProfileReaction_pointwise (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (l : C(Set.Icc (0 : ℝ) T, {L : ℝ // 1 ≤ L}))
    (q g : C(Set.Icc (0 : ℝ) T, FourierL2))
    (t : Set.Icc (0 : ℝ) T) (v : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k (l t).1
      (expandingProfileReaction a k T ha ha1 hk m l q g (t, v)) x =
      -Complex.I * oddPowerDerivative m
        (expandingTorusFunction a k (l t).1 (q t) x)
        (expandingTorusFunction a k (l t).1 v x) +
        expandingTorusFunction a k (l t).1 (g t) x := by
  rw [expandingTorusFunction_eq_evaluation a k (l t).1 ha ha1 hk (l t).2]
  change expandingPointEvaluation a k (l t).1 ha ha1 hk (l t).2 x
    (-Complex.I • _ + g t) = _
  rw [map_add, map_smul]
  simp only [← expandingTorusFunction_eq_evaluation a k (l t).1 ha ha1 hk (l t).2,
    smul_eq_mul, expandingOddPower_fderiv_pointwise]

/-- Uniform short-slab existence for the actual varying-scale linearized potential. -/
theorem exists_expandingProfile_mild_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T), T * K < 1 →
      ∀ (q g : C(Set.Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2),
      (∀ t, ‖q t‖ ≤ R) →
      ∃! u : C(Set.Icc (0 : ℝ) T, FourierL2), ∀ t : Set.Icc (0 : ℝ) T,
        u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory T hT
              (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g) u) := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingProfileReaction_lipschitz a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT hTK q g u₀ hq
  exact existsUnique_expandingMildSolution a b k L T ha hk hL hT
    (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g)
    u₀ K hK hTK (hbound T (expandingRadiusCurve L T hL) q g hq)

end DefocusingNLS

end OAI
