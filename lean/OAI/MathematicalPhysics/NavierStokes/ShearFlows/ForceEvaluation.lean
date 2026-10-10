import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveInterface

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology


open Set Filter
open scoped BigOperators Topology ContDiff
namespace ShearFlows

def IsFastRealName (a : ℕ → ℚ) (r : ℝ) : Prop :=
  ∀ n, |r - (a n : ℝ)| ≤ errorTolerance n

theorem mixedDerivative_append (V : Velocity) (α β : List (Fin 4)) :
    mixedDerivative (mixedDerivative V β) α = mixedDerivative V (α ++ β) := by
  induction α with
  | nil => rfl
  | cons j α h => simp only [mixedDerivative, List.cons_append, h]

theorem mixedDerivative_sub {V W : Velocity} (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (α : List (Fin 4)) :
    mixedDerivative (V-W) α = mixedDerivative V α - mixedDerivative W α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    simp only [mixedDerivative, ih]
    rw [fderiv_sub ((mixedDerivative_smooth hV α).differentiable (by simp) y)
      ((mixedDerivative_smooth hW α).differentiable (by simp) y)]
    rfl

theorem mixedDerivative_smul {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (r : ℝ) (α : List (Fin 4)) :
    mixedDerivative (r • V) α = r • mixedDerivative V α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    simp only [mixedDerivative, ih]
    rw [fderiv_const_smul ((mixedDerivative_smooth hV α).differentiable (by simp) y)]
    rfl

theorem mixedDerivative_sum {ι : Type*} [Fintype ι] (W : ι → Velocity)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (α : List (Fin 4)) :
    mixedDerivative (∑ i, W i) α = ∑ i, mixedDerivative (W i) α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    simp only [mixedDerivative, ih]
    rw [fderiv_sum (fun i (_ : i ∈ Finset.univ) =>
      (mixedDerivative_smooth (hW i) α).differentiable (by simp) y)]
    simp only [sum_apply, Finset.sum_apply]

theorem mixedDerivative_force {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ν : ℝ) (α : List (Fin 4)) (y : SpaceTime) :
    mixedDerivative (force ν V) α y = mixedDerivative V (α ++ [0]) y -
      ν • ∑ j : Fin 3, mixedDerivative V (α ++ [j.succ,j.succ]) y := by
  have he : force ν V = mixedDerivative V [0] -
      ν • ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ] := by
    funext z
    simpa only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply] using force_eq_mixed hV ν z
  have hs : ContDiff ℝ ∞ (∑ j : Fin 3, mixedDerivative V [j.succ,j.succ]) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        mixedDerivative_smooth hV [j.succ,j.succ]))
  have hνs : ContDiff ℝ ∞ (ν • ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ]) := by
    simpa only [Pi.smul_def] using hs.const_smul ν
  rw [he, mixedDerivative_sub (mixedDerivative_smooth hV [0]) hνs,
    mixedDerivative_smul hs,
    mixedDerivative_sum (fun j : Fin 3 => mixedDerivative V [j.succ,j.succ]) (fun j => mixedDerivative_smooth hV [j.succ,j.succ])]
  simp only [mixedDerivative_append, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]

namespace VelocityExpr

def forceCode (c : VelocityExpr) (r : ℚ) : VelocityExpr :=
  letI := neZeroFour
  fun k =>
    .add ((c k).diffWord [0]) (.mul (.const (-r))
      (FieldExpr.sum (List.ofFn (fun j : Fin 3 => (c k).diffWord [j.succ,j.succ]))))

theorem forceCode_valid {c : VelocityExpr} (hc : c.Valid) (r : ℚ) :
    (c.forceCode r).Valid := by
  intro k
  refine ⟨FieldExpr.valid_diffWord (hc k) _, trivial, FieldExpr.sum_ofFn_valid _ ?_⟩
  intro j
  exact FieldExpr.valid_diffWord (hc k) _

theorem forceCode_val {c : VelocityExpr} (hc : c.Valid) (r : ℚ) :
    (c.forceCode r).val = force r c.val := by
  funext y k
  rw [force_eq_mixed (smooth hc)]
  simp only [forceCode, val, FieldExpr.val, FieldExpr.sum_ofFn_val, Rat.cast_neg]
  have h (α : List (Fin 4)) : ((c k).diffWord α).val y = mixedDerivative c.val α y k :=
    congrFun (congrFun (val_diffWord hc α) y) k
  change ((c k).diffWord [0]).val y + -(r : ℝ) *
    (∑ j : Fin 3, ((c k).diffWord [j.succ,j.succ]).val y) = _
  simp only [h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  ring

def laplaceBound (c : VelocityExpr) (α : List (Fin 4)) : ℕ :=
  ∑ j : Fin 3, c.bound (α ++ [j.succ,j.succ])

theorem laplaceBound_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) (y : SpaceTime) :
    ‖∑ j : Fin 3, mixedDerivative c.val (α ++ [j.succ,j.succ]) y‖ ≤
      (c.laplaceBound α : ℝ) := by
  apply (norm_sum_le _ _).trans
  simpa only [laplaceBound, Nat.cast_sum] using
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => val_bound hc (α ++ [j.succ,j.succ]) y)

theorem force_coefficient_error {c : VelocityExpr} (hc : c.Valid)
    (α : List (Fin 4)) (y : SpaceTime) (ν r : ℝ) :
    ‖mixedDerivative (force ν c.val) α y - mixedDerivative (force r c.val) α y‖ ≤
      |ν-r| * (c.laplaceBound α : ℝ) := by
  rw [mixedDerivative_force (smooth hc), mixedDerivative_force (smooth hc)]
  have he {v w : Space} : (v - ν • w) - (v - r • w) = (r-ν) • w := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (laplaceBound_spec hc α y) (abs_nonneg _)

def forceBound (c : VelocityExpr) (α : List (Fin 4)) (a : ℕ → ℚ) : ℕ :=
  letI := neZeroFour
  ⌈(c.bound (α ++ [0]) : ℚ) + (|a 0|+1) * (c.laplaceBound α : ℚ)⌉₊

theorem forceBound_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν) (y : SpaceTime) :
    ‖mixedDerivative (force ν c.val) α y‖ ≤ (c.forceBound α a : ℝ) := by
  have hν : |ν| ≤ |(a 0 : ℝ)|+1 := by
    have hh := ha 0
    simp only [errorTolerance, pow_zero, inv_one] at hh
    linarith [abs_sub_abs_le_abs_sub ν (a 0)]
  rw [mixedDerivative_force (smooth hc)]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs]
  have hh := add_le_add (val_bound hc (α ++ [0]) y)
    (mul_le_mul hν (laplaceBound_spec hc α y) (norm_nonneg _) (by positivity))
  apply hh.trans
  exact_mod_cast (Nat.le_ceil ((c.bound (α ++ [0]) : ℚ) + (|a 0|+1)*(c.laplaceBound α : ℚ)))

def coefficientPrecision (c : VelocityExpr) (α : List (Fin 4)) (ε : ℚ) : ℕ :=
  ⌈2 * (c.laplaceBound α : ℚ) / ε⌉₊ + 1

theorem coefficientPrecision_spec (c : VelocityExpr) (α : List (Fin 4))
    {ε : ℚ} (hε : 0 < ε) :
    errorTolerance (c.coefficientPrecision α ε) * (c.laplaceBound α : ℝ) ≤ (ε : ℝ)/2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : (2 * (c.laplaceBound α : ℝ) / ε) ≤ (c.coefficientPrecision α ε : ℝ) := by
    have hh : 2 * (c.laplaceBound α : ℚ) / ε ≤ (c.coefficientPrecision α ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [coefficientPrecision])
    exact_mod_cast hh
  have hp : (c.coefficientPrecision α ε : ℝ) ≤ (2 : ℝ)^(c.coefficientPrecision α ε) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := c.coefficientPrecision α ε)).le
  have hle := hn.trans hp
  have h2 : (0 : ℝ) < 2^(c.coefficientPrecision α ε) := by positivity
  rw [errorTolerance, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ h2).2
  have hh := (div_le_iff₀ he).1 hle
  linarith

theorem rational_half_pos {ε : ℚ} (hε : 0 < ε) : 0 < ε / (2 : ℕ) :=
  half_pos hε

def evaluateForce (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  letI := twoAtLeastTwo
  let r := a (c.coefficientPrecision α ε)
  (c.forceCode r).evaluate (forceCode_valid hc r) α b (ε/2) (rational_half_pos hε)

theorem evaluateForce_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (force ν c.val) α y -
      rationalVector (c.evaluateForce hc α a b ε hε)‖ ≤ (ε : ℝ) := by
  let r := a (c.coefficientPrecision α ε)
  calc
    _ ≤ ‖mixedDerivative (force ν c.val) α y - mixedDerivative (force r c.val) α y‖ +
        ‖mixedDerivative (force r c.val) α y -
          rationalVector (c.evaluateForce hc α a b ε hε)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε : ℝ)/2 + (ε : ℝ)/2 := by
      apply add_le_add
      · exact (force_coefficient_error hc α y ν r).trans
          ((mul_le_mul_of_nonneg_right (ha _) (Nat.cast_nonneg _)).trans (coefficientPrecision_spec c α hε))
      · simpa only [evaluateForce, forceCode_val hc, Rat.cast_div, Rat.cast_ofNat] using
          evaluate_spec (forceCode_valid hc r) α b hb (ε/2) (by positivity)
    _ = _ := by ring

end VelocityExpr

structure HasEffectiveForce (ν : ℝ) (V : Velocity) (c : VelocityExpr) : Prop where
  valid : c.Valid
  evaluation : ∀ (α : List (Fin 4)) (a : ℕ → ℚ), IsFastRealName a ν →
    ∀ (b : ℕ → RationalSpaceTime) (y : SpaceTime), IsFastName b y →
    ∀ (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative (force ν V) α y -
        rationalVector (c.evaluateForce valid α a b ε hε)‖ ≤ (ε : ℝ)
  bound : ∀ (α : List (Fin 4)) (a : ℕ → ℚ), IsFastRealName a ν → ∀ (y : SpaceTime),
    ‖mixedDerivative (force ν V) α y‖ ≤ (c.forceBound α a : ℝ)

theorem compileShears_force_effective {d : Input} (hd : ValidInput d) (ν : ℝ) :
    HasEffectiveForce ν d.realizingVelocity (compileShears d).code := by
  have hc := velocityExpr_valid hd
  refine ⟨hc, ?_, ?_⟩
  · intro α a ha b y hb ε hε
    simpa only [compileShears, ← velocityExpr_val hd] using
      VelocityExpr.evaluateForce_spec hc α ha hb ε hε
  · intro α a ha y
    simpa only [compileShears, ← velocityExpr_val hd] using
      VelocityExpr.forceBound_spec hc α ha y

end ShearFlows

end

end OAI
