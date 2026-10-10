import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelContinuity
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # A short-time mild contraction on expanding tori

A jointly continuous reaction with a uniform Lipschitz bound gives a unique
mild trajectory whenever `T K < 1`.  The interval length depends on the
reaction bound and is independent of the starting torus scale.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

noncomputable def expandingReactionHistory (T : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u : C(Icc (0 : ℝ) T, FourierL2)) : ℝ → FourierL2 :=
  fun t => F (projIcc 0 T hT t, u (projIcc 0 T hT t))

theorem continuous_expandingReactionHistory (T : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    Continuous (expandingReactionHistory T hT F u) :=
  F.continuous.comp (continuous_projIcc.prodMk (u.continuous.comp continuous_projIcc))

noncomputable def expandingPicard (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
    expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u)
  continuous_toFun := by
    have hp : Continuous (fun t : Icc (0 : ℝ) T =>
        ((⟨L, hL⟩, ⟨t.1, t.2.1⟩) : ExpandingFreeParameters)) :=
      continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
    exact ((continuous_expandingFreeFamily a b k ha hk u₀).comp hp).add
      ((continuous_expandingDuhamel a b k ha hk _
        (continuous_expandingReactionHistory T hT F u)).comp hp)

/-- The Picard contraction constant is `T K`, with no dependence on `L`. -/
theorem expandingPicard_dist_le (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, FourierL2)) :
    dist (expandingPicard a b k L T ha hk hL hT F u₀ u)
      (expandingPicard a b k L T ha hk hL hT F u₀ v) ≤ T * K * dist u v := by
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  let ru := expandingReactionHistory T hT F u
  let rv := expandingReactionHistory T hT F v
  have hru : Continuous ru := continuous_expandingReactionHistory T hT F u
  have hrv : Continuous rv := continuous_expandingReactionHistory T hT F v
  have hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖ru τ - rv τ‖ ≤ K * dist u v := by
    intro τ hτ
    change ‖F (projIcc 0 T hT τ, _) - F (projIcc 0 T hT τ, _)‖ ≤ _
    exact (hF _ _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using
        (ContinuousMap.dist_apply_le_dist (f := u) (g := v) (projIcc 0 T hT τ))) hK)
  have hb := expandingDuhamel_norm_le_mul a b k L ha hk hL t (K * dist u v)
    t.2.1 (fun τ => ru τ - rv τ) (hru.sub hrv).continuousOn hbound
  change dist
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t ru)
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t rv) ≤ _
  rw [dist_add_left, dist_eq_norm,
    ← expandingDuhamel_sub a b k L ha hk hL t ru rv hru.continuousOn hrv.continuousOn]
  apply hb.trans
  calc
    (t : ℝ) * (K * dist u v) ≤ T * (K * dist u v) :=
      mul_le_mul_of_nonneg_right t.2.2 (mul_nonneg hK dist_nonneg)
    _ = _ := by ring

/-- Existence and uniqueness of the actual moving-scale mild equation on a short slab. -/
theorem existsUnique_expandingMildSolution (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (hTK : T * K < 1)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖) :
    ∃! u : C(Icc (0 : ℝ) T, FourierL2), ∀ t : Icc (0 : ℝ) T,
      u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u) := by
  let P := expandingPicard a b k L T ha hk hL hT F u₀
  have hP : ContractingWith ⟨T * K, mul_nonneg hT hK⟩ P :=
    ⟨hTK, LipschitzWith.of_dist_le_mul
      (expandingPicard_dist_le a b k L T ha hk hL hT F u₀ K hK hF)⟩
  refine ⟨hP.fixedPoint P, ?_, ?_⟩
  · intro t
    exact (congrArg (fun u : C(Icc (0 : ℝ) T, FourierL2) => u t)
      hP.fixedPoint_isFixedPt).symm
  · intro u hu
    apply hP.fixedPoint_unique
    apply ContinuousMap.ext
    intro t
    exact (hu t).symm

/-- Short-slab dependence on the initial datum is uniform in the torus scale. -/
theorem expandingMildSolution_initialData_bound (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u₀ v₀ : FourierL2) (K : ℝ) (hK : 0 ≤ K) (hTK : T * K < 1)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ t : Icc (0 : ℝ) T, u t =
      expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u))
    (hv : ∀ t : Icc (0 : ℝ) T, v t =
      expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F v)) :
    dist u v ≤ dist u₀ v₀ / (1 - T * K) := by
  let P := expandingPicard a b k L T ha hk hL hT F u₀
  let Q := expandingPicard a b k L T ha hk hL hT F v₀
  have hP : ContractingWith ⟨T * K, mul_nonneg hT hK⟩ P :=
    ⟨hTK, LipschitzWith.of_dist_le_mul
      (expandingPicard_dist_le a b k L T ha hk hL hT F u₀ K hK hF)⟩
  have huP : Function.IsFixedPt P u := by
    apply ContinuousMap.ext
    intro t
    exact (hu t).symm
  have hvQ : Function.IsFixedPt Q v := by
    apply ContinuousMap.ext
    intro t
    exact (hv t).symm
  apply hP.dist_fixedPoint_fixedPoint_of_dist_le' Q huP hvQ
  intro z
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro t
  change dist
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F z))
    (expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F z)) ≤ _
  rw [dist_add_right, dist_eq_norm, ← map_sub]
  apply (expandingFreeStep_norm_bound a b k L t ha hk hL t.2.1 (u₀ - v₀)).trans
  rw [dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith [t.2.1]))

/-- The real-linear potential enters with the exact Schrödinger factor `-i`. -/
noncomputable def expandingLinearReaction (T : ℝ)
    (B : C(Icc (0 : ℝ) T, FourierL2 →L[ℝ] FourierL2))
    (g : C(Icc (0 : ℝ) T, FourierL2)) :
    C((Icc (0 : ℝ) T) × FourierL2, FourierL2) where
  toFun p := -Complex.I • B p.1 p.2 + g p.1
  continuous_toFun :=
    (((B.continuous.comp continuous_fst).clm_apply continuous_snd).const_smul (-Complex.I : ℂ)).add
      (g.continuous.comp continuous_fst)

theorem expandingLinearReaction_lipschitz (T : ℝ)
    (B : C(Icc (0 : ℝ) T, FourierL2 →L[ℝ] FourierL2))
    (g : C(Icc (0 : ℝ) T, FourierL2)) (K : ℝ)
    (hB : ∀ t, ‖B t‖ ≤ K) (t : Icc (0 : ℝ) T) (x y : FourierL2) :
    ‖expandingLinearReaction T B g (t, x) - expandingLinearReaction T B g (t, y)‖ ≤
      K * ‖x - y‖ := by
  change ‖(-Complex.I • B t x + g t) - (-Complex.I • B t y + g t)‖ ≤ _
  rw [add_sub_add_right_eq_sub, ← smul_sub, ← map_sub, norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact ((B t).le_opNorm (x - y)).trans
    (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _))

/-- Uniformly bounded continuous real-linear potentials have a unique short-slab
propagator, including a continuous source term. -/
theorem existsUnique_expandingLinearMildSolution (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (B : C(Icc (0 : ℝ) T, FourierL2 →L[ℝ] FourierL2))
    (g : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (hTK : T * K < 1) (hB : ∀ t, ‖B t‖ ≤ K) :
    ∃! u : C(Icc (0 : ℝ) T, FourierL2), ∀ t : Icc (0 : ℝ) T,
      u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT (expandingLinearReaction T B g) u) :=
  existsUnique_expandingMildSolution a b k L T ha hk hL hT
    (expandingLinearReaction T B g) u₀ K hK hTK (expandingLinearReaction_lipschitz T B g K hB)

end DefocusingNLS

end OAI
