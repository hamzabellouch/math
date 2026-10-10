import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFiniteSlab
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelLinear

namespace OAI

/-! # The finite-slab propagator for the actual linearized profile

The solution operator is real-linear and bounded in the exact expanding
Sobolev coordinates. Its bound depends on the profile bound and elapsed
time, and is independent of the starting radius.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

section Trajectory

variable (a b k L T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (hL : 1 ≤ L) (hT : 0 ≤ T) (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
  (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ t, ‖q t‖ ≤ R)

local notation "F" => expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0

noncomputable def expandingProfileTrajectory (u₀ : FourierL2) :
    C(Icc (0 : ℝ) T, FourierL2) :=
  Classical.choose (existsUnique_expandingProfile_finiteSlab a b k L T ha ha1 hk hL hT
    m R hR q 0 u₀ hq).exists

local notation "S" => expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq

theorem expandingProfileTrajectory_eq (u₀ : FourierL2) (t : Icc (0 : ℝ) T) :
    S u₀ t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F (S u₀)) :=
  Classical.choose_spec (existsUnique_expandingProfile_finiteSlab a b k L T ha ha1 hk hL hT
    m R hR q 0 u₀ hq).exists t

theorem expandingProfileTrajectory_unique (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ t : Icc (0 : ℝ) T, u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u)) :
    u = S u₀ :=
  (existsUnique_expandingProfile_finiteSlab a b k L T ha ha1 hk hL hT m R hR q 0 u₀ hq).unique
    hu (expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq u₀)

private theorem profile_history_zero : expandingReactionHistory T hT F 0 = fun _ => 0 := by
  funext τ
  let τ' := projIcc 0 T hT τ
  let l := expandingRadiusCurve L T hL
  let D : FourierL2 →L[ℝ] FourierL2 :=
    fderiv ℝ (expandingOddPower a k (l τ').1 ha ha1 hk (l τ').2 m) (q τ')
  change -Complex.I • D 0 + 0 = 0
  simp only [map_zero, smul_zero, add_zero]

private theorem profile_history_add (u v : C(Icc (0 : ℝ) T, FourierL2)) :
    expandingReactionHistory T hT F (u + v) = fun τ =>
      expandingReactionHistory T hT F u τ + expandingReactionHistory T hT F v τ := by
  funext τ
  let τ' := projIcc 0 T hT τ
  let l := expandingRadiusCurve L T hL
  let D : FourierL2 →L[ℝ] FourierL2 :=
    fderiv ℝ (expandingOddPower a k (l τ').1 ha ha1 hk (l τ').2 m) (q τ')
  change -Complex.I • D (u τ' + v τ') + 0 =
    (-Complex.I • D (u τ') + 0) + (-Complex.I • D (v τ') + 0)
  simp only [map_add, smul_add, add_zero]

private theorem profile_history_smul (c : ℝ) (u : C(Icc (0 : ℝ) T, FourierL2)) :
    expandingReactionHistory T hT F (c • u) = fun τ =>
      c • expandingReactionHistory T hT F u τ := by
  funext τ
  let τ' := projIcc 0 T hT τ
  let l := expandingRadiusCurve L T hL
  let D : FourierL2 →L[ℝ] FourierL2 :=
    fderiv ℝ (expandingOddPower a k (l τ').1 ha ha1 hk (l τ').2 m) (q τ')
  change -Complex.I • D (c • u τ') + 0 =
    c • (-Complex.I • D (u τ') + 0)
  simp only [map_smul, add_zero]
  exact smul_comm _ _ _

@[simp] theorem expandingProfileTrajectory_zero : S 0 = 0 := by
  symm
  apply expandingProfileTrajectory_unique a b k L T ha ha1 hk hL hT m R hR q hq
  intro t
  rw [profile_history_zero a k L T ha ha1 hk hL hT m q,
    expandingDuhamel_zero, map_zero, add_zero]
  rfl

theorem expandingProfileTrajectory_add (u₀ v₀ : FourierL2) : S (u₀ + v₀) = S u₀ + S v₀ := by
  symm
  apply expandingProfileTrajectory_unique a b k L T ha ha1 hk hL hT m R hR q hq
  intro t
  rw [profile_history_add a k L T ha ha1 hk hL hT m q,
    expandingDuhamel_add a b k L ha hk hL t _ _
      (continuous_expandingReactionHistory T hT F (S u₀)).continuousOn
      (continuous_expandingReactionHistory T hT F (S v₀)).continuousOn, map_add]
  change S u₀ t + S v₀ t = _
  rw [expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq u₀,
    expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq v₀]
  abel

theorem expandingProfileTrajectory_smul (c : ℝ) (u₀ : FourierL2) : S (c • u₀) = c • S u₀ := by
  symm
  apply expandingProfileTrajectory_unique a b k L T ha ha1 hk hL hT m R hR q hq
  intro t
  rw [profile_history_smul a k L T ha ha1 hk hL hT m q,
    expandingDuhamel_real_smul, ContinuousLinearMap.map_smul_of_tower]
  change c • S u₀ t = _
  rw [expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq u₀, smul_add]

end Trajectory

/-- One uniform growth rate yields bounded real-linear finite-slab propagators
for every permitted radius and bounded continuous profile. -/
theorem exists_expandingProfile_propagator (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
      (q : C(Icc (0 : ℝ) T, FourierL2)) (_hq : ∀ t, ‖q t‖ ≤ R),
      ∃ U : FourierL2 →L[ℝ] C(Icc (0 : ℝ) T, FourierL2),
        (∀ u₀ t, U u₀ t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0) (U u₀))) ∧
        ‖U‖ ≤ (K + 1) * Real.exp ((K + 1) * T) := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingProfileReaction_lipschitz a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT q hq
  let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m R hR q hq
  let F := expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0
  let A : FourierL2 →ₗ[ℝ] C(Icc (0 : ℝ) T, FourierL2) :=
    { toFun := S
      map_add' := expandingProfileTrajectory_add a b k L T ha ha1 hk hL hT m R hR q hq
      map_smul' := expandingProfileTrajectory_smul a b k L T ha ha1 hk hL hT m R hR q hq }
  have hC : 0 ≤ (K + 1) * Real.exp ((K + 1) * T) := by positivity
  have hA : ∀ u₀, ‖A u₀‖ ≤ (K + 1) * Real.exp ((K + 1) * T) * ‖u₀‖ := by
    intro u₀
    have h := expandingMildSolution_finiteSlab_initialData_bound a b k L T ha hk hL hT F
      u₀ 0 K hK (hbound T (expandingRadiusCurve L T hL) q 0 hq) (S u₀) (S 0)
      (expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq u₀)
      (expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq 0)
    simpa only [A, LinearMap.coe_mk, AddHom.coe_mk, S, expandingProfileTrajectory_zero, dist_zero_right] using h
  let U := A.mkContinuous ((K + 1) * Real.exp ((K + 1) * T)) hA
  refine ⟨U, ?_, LinearMap.mkContinuous_norm_le _ hC hA⟩
  exact expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m R hR q hq

end DefocusingNLS

end OAI
