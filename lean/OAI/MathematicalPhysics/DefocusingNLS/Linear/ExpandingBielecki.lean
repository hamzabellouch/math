import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightedDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildContraction

namespace OAI

/-! # The moving-scale mild equation on arbitrary finite slabs

An exponential time weight makes the Picard map contract with constant
`K / (K + 1)` on every finite interval.  Thus the permitted slab length is
independent of the initial radius and requires no a priori small-time bound.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

noncomputable def expandingTimeWeight (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := Real.exp (η * t) • u t
  continuous_toFun :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul u.continuous

@[simp] theorem expandingTimeWeight_cancel (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    expandingTimeWeight T η (expandingTimeWeight T (-η) u) = u := by
  apply ContinuousMap.ext
  intro t
  change Real.exp (η * t) • (Real.exp (-η * t) • u t) = u t
  rw [smul_smul, ← Real.exp_add, show η * (t : ℝ) + -η * t = 0 by ring, Real.exp_zero, one_smul]

noncomputable def expandingBieleckiHistory (T η : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u : C(Icc (0 : ℝ) T, FourierL2)) : ℝ → FourierL2 :=
  expandingReactionHistory T hT F (expandingTimeWeight T η u)

theorem continuous_expandingBieleckiHistory (T η : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    Continuous (expandingBieleckiHistory T η hT F u) :=
  continuous_expandingReactionHistory T hT F _

noncomputable def expandingBieleckiPicard (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) :=
  expandingTimeWeight T (-η)
    (expandingPicard a b k L T ha hk hL hT F u₀ (expandingTimeWeight T η u))

/-- The weighted Picard bound is independent of both radius and slab length. -/
theorem expandingBieleckiPicard_dist_le (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (hη : 0 < η)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, FourierL2)) :
    dist (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ u)
      (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ v) ≤ K / η * dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (div_nonneg hK hη.le) dist_nonneg)).2
  intro t
  let ru := expandingBieleckiHistory T η hT F u
  let rv := expandingBieleckiHistory T η hT F v
  have hru : Continuous ru := continuous_expandingBieleckiHistory T η hT F u
  have hrv : Continuous rv := continuous_expandingBieleckiHistory T η hT F v
  have hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖ru τ - rv τ‖ ≤ (K * dist u v) * Real.exp (η * τ) := by
    intro τ hτ
    let τ' : Icc (0 : ℝ) T := ⟨τ, hτ.1, hτ.2.trans t.2.2⟩
    have hτT : τ ∈ Icc 0 T := τ'.2
    change ‖F (projIcc 0 T hT τ, _) - F (projIcc 0 T hT τ, _)‖ ≤ _
    have hnorm : ‖expandingTimeWeight T η u (projIcc 0 T hT τ) -
        expandingTimeWeight T η v (projIcc 0 T hT τ)‖ ≤
        Real.exp (η * τ) * dist u v := by
      rw [projIcc_of_mem _ hτT]
      change ‖Real.exp (η * τ) • u τ' - Real.exp (η * τ) • v τ'‖ ≤ _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := u) (g := v) τ'))
        (Real.exp_pos _).le
    calc
      _ ≤ K * ‖expandingTimeWeight T η u (projIcc 0 T hT τ) -
          expandingTimeWeight T η v (projIcc 0 T hT τ)‖ := hF _ _ _
      _ ≤ K * (Real.exp (η * τ) * dist u v) := mul_le_mul_of_nonneg_left hnorm hK
      _ = _ := by ring
  have hb := expandingDuhamel_weighted_norm_le a b k L η t (K * dist u v)
    ha hk hL hη t.2.1 (mul_nonneg hK dist_nonneg) (fun τ => ru τ - rv τ) hbound
  change dist
    (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t ru))
    (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t rv)) ≤ _
  rw [dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    ← expandingDuhamel_sub a b k L ha hk hL t ru rv hru.continuousOn hrv.continuousOn]
  calc
    _ ≤ (K * dist u v) / η := hb
    _ = _ := by ring

/-- Globally Lipschitz continuous reactions have a unique moving-scale mild solution
on every finite slab.  In particular, the actual bounded linearized potential does. -/
theorem existsUnique_expandingMildSolution_finiteSlab (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖) :
    ∃! u : C(Icc (0 : ℝ) T, FourierL2), ∀ t : Icc (0 : ℝ) T,
      u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u) := by
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  have hKl : 0 ≤ K / η := div_nonneg hK hη.le
  have hKl' : K / η < 1 := (div_lt_one hη).2 (by dsimp [η]; linarith)
  let P := expandingBieleckiPicard a b k L T η ha hk hL hT F u₀
  have hP : ContractingWith ⟨K / η, hKl⟩ P :=
    ⟨hKl', LipschitzWith.of_dist_le_mul
      (expandingBieleckiPicard_dist_le a b k L T η ha hk hL hT hη F u₀ K hK hF)⟩
  let v := hP.fixedPoint P
  have hv : P v = v := hP.fixedPoint_isFixedPt
  let u := expandingTimeWeight T η v
  refine ⟨u, ?_, ?_⟩
  · intro t
    have he := congrArg (fun f : C(Icc (0 : ℝ) T, FourierL2) => expandingTimeWeight T η f t) hv
    change u t = expandingPicard a b k L T ha hk hL hT F u₀ u t
    simpa only [P, expandingBieleckiPicard, expandingTimeWeight_cancel, u] using he.symm
  · intro w hw
    let z := expandingTimeWeight T (-η) w
    have hz : Function.IsFixedPt P z := by
      apply ContinuousMap.ext
      intro t
      change Real.exp (-η * t) •
        (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory T hT F (expandingTimeWeight T η z))) = z t
      rw [show expandingTimeWeight T η z = w from expandingTimeWeight_cancel T η w]
      rw [← hw t]
      rfl
    have he : z = v := hP.fixedPoint_unique hz
    have h := congrArg (expandingTimeWeight T η) he
    simpa only [z, expandingTimeWeight_cancel, u] using h

end DefocusingNLS

end OAI
