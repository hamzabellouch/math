import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ExpressionCompiler

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

section PartEffectiveInterface

open Set Filter
open scoped BigOperators Topology ContDiff
namespace ShearFlows

abbrev RationalSpaceTime := ℚ × (Fin 3 → ℚ)
abbrev RationalVector := Fin 3 → ℚ

def rationalVector (a : RationalVector) : Space := fun k => (a k : ℝ)

def IsFastName (a : ℕ → RationalSpaceTime) (y : SpaceTime) : Prop :=
  ∀ n, ‖y - rationalPoint (a n)‖ ≤ errorTolerance n

theorem timeSpaceCoord_norm (j : Fin 4) (v : SpaceTime) :
    ‖timeSpaceCoord j v‖ ≤ ‖v‖ := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact norm_fst_le v
  · exact (norm_le_pi_norm v.2 k).trans (norm_snd_le v)

theorem spaceTimeDirections_sum (v : SpaceTime) :
    (∑ j : Fin 4, timeSpaceCoord j v • spaceTimeDirection j) = v := by
  apply Prod.ext
  · simp [Fin.sum_univ_succ, timeSpaceCoord, spaceTimeDirection]
  · ext k
    fin_cases k <;> simp [Fin.sum_univ_succ, timeSpaceCoord, spaceTimeDirection, basis]

namespace VelocityExpr

def modulusBound (c : VelocityExpr) (α : List (Fin 4)) : ℕ :=
  ∑ j : Fin 4, c.bound (j :: α)

theorem fderiv_bound {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) (y : SpaceTime) :
    ‖fderiv ℝ (mixedDerivative c.val α) y‖ ≤ (c.modulusBound α : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j : Fin 4, ‖(fderiv ℝ (mixedDerivative c.val α) y)
        (timeSpaceCoord j v • spaceTimeDirection j)‖) ≤
        ∑ j : Fin 4, ‖v‖ * (c.bound (j :: α) : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul]
      exact mul_le_mul (timeSpaceCoord_norm j v) (c.val_bound hc (j :: α) y)
        (norm_nonneg _) (norm_nonneg _)
    _ = (c.modulusBound α : ℝ) * ‖v‖ := by simp [modulusBound, Finset.sum_mul, mul_comm]

theorem lipschitz_bound {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) (x y : SpaceTime) :
    ‖mixedDerivative c.val α x - mixedDerivative c.val α y‖ ≤
      (c.modulusBound α : ℝ) * ‖x-y‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set SpaceTime)) =>
      (mixedDerivative_smooth (smooth hc) α).differentiable (by simp) z)
    (fun z _ => fderiv_bound hc α z) (convex_univ) (mem_univ y) (mem_univ x)

def inputPrecision (c : VelocityExpr) (α : List (Fin 4)) (ε : ℚ) : ℕ :=
  ⌈2 * (c.modulusBound α : ℚ) / ε⌉₊ + 1

theorem inputPrecision_spec (c : VelocityExpr) (α : List (Fin 4)) {ε : ℚ} (hε : 0 < ε) :
    (c.modulusBound α : ℝ) * errorTolerance (c.inputPrecision α ε) ≤ (ε : ℝ)/2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : (2 * (c.modulusBound α : ℝ) / ε) ≤ (c.inputPrecision α ε : ℝ) := by
    have hh : 2 * (c.modulusBound α : ℚ) / ε ≤ (c.inputPrecision α ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [inputPrecision])
    exact_mod_cast hh
  have hp : (c.inputPrecision α ε : ℝ) ≤ (2 : ℝ)^(c.inputPrecision α ε) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := c.inputPrecision α ε)).le
  have hle := hn.trans hp
  have h2 : (0 : ℝ) < 2^(c.inputPrecision α ε) := by positivity
  rw [errorTolerance, ← div_eq_mul_inv]
  apply (div_le_iff₀ h2).2
  have hh := (div_le_iff₀ he).1 hle
  linarith

def Ready (c : VelocityExpr) (α : List (Fin 4)) (q : RationalSpaceTime) (ε : ℚ) (n : ℕ) : Prop :=
  ∀ k : Fin 3, (((c k).diffWord α).enclose q n).radius ≤ ε

instance (c : VelocityExpr) (α : List (Fin 4)) (q : RationalSpaceTime) (ε : ℚ) (n : ℕ) :
    Decidable (c.Ready α q ε n) := inferInstanceAs (Decidable (∀ _ : Fin 3, _ ≤ _))

theorem ready_exists {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    (q : RationalSpaceTime) {ε : ℚ} (hε : 0 < ε) : ∃ n, c.Ready α q ε n := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hh (k : Fin 3) : ∀ᶠ n in atTop,
      (((c k).diffWord α).enclose q n).radius ≤ ε := by
    have ht := (FieldExpr.enclose_converges (FieldExpr.valid_diffWord (hc k) α) q).2
    filter_upwards [ht.eventually_lt_const he] with n hn
    exact_mod_cast hn.le
  exact ((Filter.eventually_all).2 hh).exists

def evaluateRational (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (q : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let n := Nat.find (ready_exists hc α q hε)
  fun k => (((c k).diffWord α).enclose q n).center

theorem evaluateRational_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    (q : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative c.val α (rationalPoint q) -
      rationalVector (c.evaluateRational hc α q ε hε)‖ ≤ (ε : ℝ) := by
  rw [← val_diffWord hc]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hε.le)).2
  intro k
  have hb := FieldExpr.enclose_contains (FieldExpr.valid_diffWord (hc k) α) q
    (Nat.find (ready_exists hc α q hε))
  have hn := Nat.find_spec (ready_exists hc α q hε) k
  exact hb.trans (by exact_mod_cast hn)

def evaluate (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  c.evaluateRational hc α (a (c.inputPrecision α ε)) (ε/2) (by positivity)

theorem evaluate_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative c.val α y - rationalVector (c.evaluate hc α a ε hε)‖ ≤ (ε : ℝ) := by
  let q := a (c.inputPrecision α ε)
  calc
    _ ≤ ‖mixedDerivative c.val α y - mixedDerivative c.val α (rationalPoint q)‖ +
        ‖mixedDerivative c.val α (rationalPoint q) -
          rationalVector (c.evaluate hc α a ε hε)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε : ℝ)/2 + (ε : ℝ)/2 := by
      apply add_le_add
      · exact (lipschitz_bound hc α y (rationalPoint q)).trans
          ((mul_le_mul_of_nonneg_left (ha _) (Nat.cast_nonneg _)).trans (inputPrecision_spec c α hε))
      · simpa only [evaluate, Rat.cast_div, Rat.cast_ofNat] using
          evaluateRational_spec hc α q (ε/2) (by positivity)
    _ = _ := by ring

end VelocityExpr

structure FinitePrescription where
  code : VelocityExpr
  radius : ℚ

def compileShears (d : Input) : FinitePrescription := ⟨d.velocityExpr, d.tubeRadius⟩

structure HasEffectiveDerivatives (V : Velocity) (c : VelocityExpr) : Prop where
  valid : c.Valid
  evaluation : ∀ (α : List (Fin 4)) (a : ℕ → RationalSpaceTime) (y : SpaceTime),
    IsFastName a y → ∀ (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative V α y - rationalVector (c.evaluate valid α a ε hε)‖ ≤ (ε : ℝ)
  bound : ∀ (α : List (Fin 4)) (y : SpaceTime),
    ‖mixedDerivative V α y‖ ≤ (c.bound α : ℝ)

theorem compileShears_effective {d : Input} (hd : ValidInput d) :
    HasEffectiveDerivatives d.realizingVelocity (compileShears d).code := by
  have hc := velocityExpr_valid hd
  refine ⟨hc, ?_, ?_⟩
  · intro α a y hy ε hε
    simpa only [compileShears, ← velocityExpr_val hd] using
      VelocityExpr.evaluate_spec hc α a hy ε hε
  · intro α y
    simpa only [compileShears, ← velocityExpr_val hd] using
      VelocityExpr.val_bound hc α y

end ShearFlows

end PartEffectiveInterface

end

end OAI
