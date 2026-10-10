import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ForceGerm
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBounds

namespace OAI

/-! Effective startup of an autonomous finite field expression. A fixed
three-region selector uses a finite transition expression near startup and
the autonomous expression on the entire late-time tail. -/

namespace ForcedComputation
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem residual_congr_germ {U V : Velocity} {t : ℝ} {x : Space}
    (he : U =ᶠ[𝓝 (t, x)] V) (ν : ℝ) : residual ν U (t, x) = residual ν V (t, x) := by
  have hx : (fun z => U (t, z)) =ᶠ[𝓝 x] fun z => V (t, z) :=
    he.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  rw [residual_eq_force_add, residual_eq_force_add]
  change force ν U (t, x) + fderiv ℝ (fun z => U (t, z)) x (U (t, x)) =
    force ν V (t, x) + fderiv ℝ (fun z => V (t, z)) x (V (t, x))
  rw [force_congr_germ he ν, hx.fderiv_eq, he.self_of_nhds]

theorem residual_eventuallyEq {U V : Velocity} {y : SpaceTime}
    (he : U =ᶠ[𝓝 y] V) (ν : ℝ) : residual ν U =ᶠ[𝓝 y] residual ν V := by
  filter_upwards [eventually_eventually_nhds.mpr he] with z hz
  exact residual_congr_germ hz ν

def startupTransition : PeriodicExpr := PeriodicExpr.cutoff 4 (1/2) 1 (3/2) 2

theorem startupTransition_valid : startupTransition.Valid :=
  PeriodicExpr.cutoff_valid (by norm_num) (by norm_num) (by norm_num)

theorem startupTransition_val {t : ℝ} (ht : t ∈ Ioo 0 (3/2)) :
    startupTransition.val t = startupRamp t := by
  have he : startupTransition.val t = closedCutoff (1/2) 1 (3/2) 2 t := by
    rw [startupTransition, PeriodicExpr.cutoff_val]
    norm_num only [Rat.cast_ofNat, Rat.cast_div]
    unfold circleCutoff
    apply periodize_eq_in_chart (A := 0) (B := 2) (by norm_num) (by norm_num)
    · intro z hz
      have hs := closedCutoff_support (by norm_num : (1/2 : ℝ) < 1)
        (by norm_num : (3/2 : ℝ) < 2) hz
      exact ⟨by linarith [hs.1], hs.2⟩
    · exact ⟨ht.1.le, by linarith [ht.2]⟩
  rw [he, closedCutoff, smoothRamp_after (by norm_num : (-2 : ℝ) < -(3/2))
    (by linarith [ht.2]), mul_one]
  unfold smoothRamp startupRamp
  congr 1
  ring

def startupCode (c : VelocityExpr) : VelocityExpr :=
  letI := ShearFlows.neZeroFour
  fun k =>
  .mul (.atom 0 startupTransition) (c k)

theorem startupCode_valid {c : VelocityExpr} (hc : c.Valid) : (startupCode c).Valid :=
  fun k => ⟨startupTransition_valid, hc k⟩

theorem startupCode_val {c : VelocityExpr} {W : Space → Space}
    (hcW : c.val = fun y => W y.2) {y : SpaceTime} (hy : y.1 ∈ Ioo 0 (3/2)) :
    (startupCode c).val y = rampVelocity startupRamp W y := by
  have hc := congrFun hcW y
  funext k
  change startupTransition.val (timeSpaceCoord 0 y) * (c k).val y = _
  rw [show timeSpaceCoord 0 y = y.1 from rfl, startupTransition_val hy]
  exact congrArg (fun v : Space => startupRamp y.1 * v k) hc

def zeroCode : VelocityExpr := fun _ => .const 0

theorem zeroCode_valid : zeroCode.Valid := fun _ => trivial

theorem zeroCode_val : zeroCode.val = fun _ => 0 := by
  funext y k
  simp [zeroCode, VelocityExpr.val, FieldExpr.val]

def startupSelectCode (c : VelocityExpr) (b : ℕ → RationalSpaceTime) : VelocityExpr :=
  if (b 6).1 ≤ 1/4 then zeroCode
  else if (b 6).1 ≤ 5/4 then startupCode c else c

theorem startupSelectCode_valid {c : VelocityExpr} (hc : c.Valid)
    (b : ℕ → RationalSpaceTime) : (startupSelectCode c b).Valid := by
  unfold startupSelectCode
  split
  · exact zeroCode_valid
  · split
    · exact startupCode_valid hc
    · exact hc

theorem startupSelectCode_germ_of_time {c : VelocityExpr} {W : Space → Space}
    (hcW : c.val = fun y => W y.2) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (ht : |y.1 - ((b 6).1 : ℝ)| ≤ (1/64 : ℝ)) :
    rampVelocity startupRamp W =ᶠ[𝓝 y] (startupSelectCode c b).val := by
  unfold startupSelectCode
  split
  · rename_i hzero
    have hq : ((b 6).1 : ℝ) ≤ 1/4 := by
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr hzero
    have hy : y.1 < 1/2 := by linarith [(abs_le.mp ht).2]
    filter_upwards [(continuous_fst.tendsto y).eventually (eventually_lt_nhds hy)] with z hz
    rw [zeroCode_val]
    have ha : startupRamp z.1 = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [rampVelocity, ha, zero_smul]
  · rename_i hzero
    split
    · rename_i htrans
      have hq₀ : (1/4 : ℝ) < (b 6).1 := by
        simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr (lt_of_not_ge hzero)
      have hq₁ : ((b 6).1 : ℝ) ≤ 5/4 := by
        simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr htrans
      have hy : y.1 ∈ Ioo 0 (3/2) :=
        ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
      filter_upwards [(continuous_fst.tendsto y).eventually (Ioo_mem_nhds hy.1 hy.2)] with z hz
      exact (startupCode_val hcW hz).symm
    · rename_i htail
      have hq : (5/4 : ℝ) < (b 6).1 := by
        simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr (lt_of_not_ge htail)
      have hy : 1 < y.1 := by linarith [(abs_le.mp ht).1]
      filter_upwards [(continuous_fst.tendsto y).eventually (eventually_gt_nhds hy)] with z hz
      rw [hcW]
      simp only [rampVelocity, startupRamp_tail hz.le, one_smul]

theorem startupSelectCode_germ {c : VelocityExpr} {W : Space → Space}
    (hcW : c.val = fun y => W y.2) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hb : IsFastName b y) :
    rampVelocity startupRamp W =ᶠ[𝓝 y] (startupSelectCode c b).val := by
  apply startupSelectCode_germ_of_time hcW
  have h := (norm_fst_le (y - rationalPoint (b 6))).trans (hb 6)
  norm_num [Prod.fst_sub, rationalPoint, Real.norm_eq_abs, errorTolerance] at h
  exact h

def evaluateStartupVelocity (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  (startupSelectCode c b).evaluate (startupSelectCode_valid hc b) α b ε hε

theorem evaluateStartupVelocity_spec {c : VelocityExpr} (hc : c.Valid)
    {W : Space → Space} (hcW : c.val = fun y => W y.2) (α : List (Fin 4))
    {b : ℕ → RationalSpaceTime} {y : SpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (rampVelocity startupRamp W) α y -
      rationalVector (evaluateStartupVelocity c hc α b ε hε)‖ ≤ (ε : ℝ) := by
  rw [(mixedDerivative_eventuallyEq (startupSelectCode_germ hcW hb) α).self_of_nhds]
  exact VelocityExpr.evaluate_spec (startupSelectCode_valid hc b) α b hb ε hε

def evaluateStartupForce (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  ResidualCode.evaluate (startupSelectCode c b) (startupSelectCode_valid hc b) α a b ε hε

theorem evaluateStartupForce_spec {c : VelocityExpr} (hc : c.Valid)
    {W : Space → Space} (hcW : c.val = fun y => W y.2) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {b : ℕ → RationalSpaceTime} {y : SpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (residual ν (rampVelocity startupRamp W)) α y -
      rationalVector (evaluateStartupForce c hc α a b ε hε)‖ ≤ (ε : ℝ) := by
  rw [(mixedDerivative_eventuallyEq
    (residual_eventuallyEq (startupSelectCode_germ hcW hb) ν) α).self_of_nhds]
  exact ResidualCode.evaluate_spec (startupSelectCode_valid hc b) α ha hb ε hε

def startupVelocityBound (c : VelocityExpr) (α : List (Fin 4)) : ℕ :=
  max (zeroCode.bound α) (max ((startupCode c).bound α) (c.bound α))

def startupForceBound (c : VelocityExpr) (α : List (Fin 4)) (a : ℕ → ℚ) : ℕ :=
  max (ResidualCode.bound zeroCode α a)
    (max (ResidualCode.bound (startupCode c) α a) (ResidualCode.bound c α a))

theorem startupSelectCode_bound_le (c : VelocityExpr) (b : ℕ → RationalSpaceTime)
    (α : List (Fin 4)) : (startupSelectCode c b).bound α ≤ startupVelocityBound c α := by
  unfold startupSelectCode startupVelocityBound
  split
  · exact le_max_left _ _
  · split
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

theorem startupSelectCode_forceBound_le (c : VelocityExpr) (b : ℕ → RationalSpaceTime)
    (α : List (Fin 4)) (a : ℕ → ℚ) :
    ResidualCode.bound (startupSelectCode c b) α a ≤ startupForceBound c α a := by
  unfold startupSelectCode startupForceBound
  split
  · exact le_max_left _ _
  · split
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

theorem exists_startup_time_approximation (y : SpaceTime) :
    ∃ b : ℕ → RationalSpaceTime, |y.1 - ((b 6).1 : ℝ)| ≤ (1/64 : ℝ) := by
  obtain ⟨q, hq₀, hq₁⟩ := exists_rat_btwn
    (show y.1 - (1/64 : ℝ) < y.1 + 1/64 by linarith)
  exact ⟨fun _ => (q, 0), abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem startupVelocityBound_spec {c : VelocityExpr} (hc : c.Valid)
    {W : Space → Space} (hcW : c.val = fun y => W y.2)
    (α : List (Fin 4)) (y : SpaceTime) :
    ‖mixedDerivative (rampVelocity startupRamp W) α y‖ ≤
      (startupVelocityBound c α : ℝ) := by
  obtain ⟨b, hb⟩ := exists_startup_time_approximation y
  rw [(mixedDerivative_eventuallyEq (startupSelectCode_germ_of_time hcW hb) α).self_of_nhds]
  exact (VelocityExpr.val_bound (startupSelectCode_valid hc b) α y).trans
    (by exact_mod_cast startupSelectCode_bound_le c b α)

theorem startupForceBound_spec {c : VelocityExpr} (hc : c.Valid)
    {W : Space → Space} (hcW : c.val = fun y => W y.2)
    (α : List (Fin 4)) {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν) (y : SpaceTime) :
    ‖mixedDerivative (residual ν (rampVelocity startupRamp W)) α y‖ ≤
      (startupForceBound c α a : ℝ) := by
  obtain ⟨b, hb⟩ := exists_startup_time_approximation y
  rw [(mixedDerivative_eventuallyEq
    (residual_eventuallyEq (startupSelectCode_germ_of_time hcW hb) ν) α).self_of_nhds]
  exact (ResidualCode.bound_spec (startupSelectCode_valid hc b) α ha y).trans
    (by exact_mod_cast startupSelectCode_forceBound_le c b α a)

end ForcedComputation

end OAI
