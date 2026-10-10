import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionPotentials
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.UnitSpatialClock

namespace OAI

/-! A finite Hamiltonian expression gives an autonomous finite velocity
expression after adding the fixed spatial clock. -/

namespace ForcedComputation
open ShearFlows MeasureTheory
open scoped ContDiff BigOperators

namespace SpatialExpression

def NoTime : FieldExpr → Prop :=
  letI := ShearFlows.neZeroFour
  FieldExpr.rec (fun _ => True) (fun j _ => j ≠ 0)
    (fun _ _ hf hg => hf ∧ hg) (fun _ _ hf hg => hf ∧ hg)

def UnitPeriods : FieldExpr → Prop :=
  FieldExpr.rec (fun _ => True) (fun _ p => p.period = 1)
    (fun _ _ hf hg => hf ∧ hg) (fun _ _ hf hg => hf ∧ hg)

theorem noTime_diff {e : FieldExpr} (he : NoTime e) (j : Fin 4) : NoTime (e.diff j) := by
  induction e with
  | const _ => trivial
  | atom i p =>
    by_cases hij : i = j
    · simpa only [FieldExpr.diff, hij, ite_true, NoTime] using he
    · simp only [FieldExpr.diff, hij, ite_false, NoTime]
  | add f g hf hg => exact ⟨hf he.1, hg he.2⟩
  | mul f g hf hg => exact ⟨⟨hf he.1, he.2⟩, ⟨he.1, hg he.2⟩⟩

noncomputable def spatialValue (e : FieldExpr) (x : Space) : ℝ := e.val (0, x)

theorem unitPeriods_periodic {e : FieldExpr} (he : UnitPeriods e) :
    CubePeriodic 1 (spatialValue e) := by
  intro x n
  induction e with
  | const _ => rfl
  | atom j p =>
    change p.period = 1 at he
    have hp (s : ℝ) (k : ℤ) : p.val (s + k) = p.val s := by
      have h := (periodize_periodic (1 : ℝ) p.body.val).int_mul k s
      simpa only [PeriodicExpr.val, he, Rat.cast_one, mul_one] using h
    fin_cases j
    · rfl
    · change p.val ((x + latticeVector 1 n) 0) = p.val (x 0)
      simpa only [latticeVector, Pi.add_apply, one_mul] using hp (x 0) (n 0)
    · change p.val ((x + latticeVector 1 n) 1) = p.val (x 1)
      simpa only [latticeVector, Pi.add_apply, one_mul] using hp (x 1) (n 1)
    · change p.val ((x + latticeVector 1 n) 2) = p.val (x 2)
      simpa only [latticeVector, Pi.add_apply, one_mul] using hp (x 2) (n 2)
  | add f g hf hg => exact congrArg₂ (· + ·) (hf he.1) (hg he.2)
  | mul f g hf hg => exact congrArg₂ (· * ·) (hf he.1) (hg he.2)

theorem noTime_val {e : FieldExpr} (he : NoTime e) (y : SpaceTime) :
    e.val y = spatialValue e y.2 := by
  induction e with
  | const _ => rfl
  | atom j p =>
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero he
    rfl
  | add f g hf hg => exact congrArg₂ (· + ·) (hf he.1) (hg he.2)
  | mul f g hf hg => exact congrArg₂ (· * ·) (hf he.1) (hg he.2)

theorem spatialValue_smooth {e : FieldExpr} (he : e.Valid) :
    ContDiff ℝ ∞ (spatialValue e) :=
  (FieldExpr.smooth he).comp (contDiff_const.prodMk contDiff_id)

theorem spatialValue_diff {e : FieldExpr} (he : e.Valid) (ht : NoTime e)
    (j : Fin 3) (y : SpaceTime) :
    (e.diff j.succ).val y = scalarD j (spatialValue e) y.2 := by
  rw [FieldExpr.val_diff he]
  have hv : e.val = fun z => spatialValue e z.2 := funext (noTime_val ht)
  have hd := ((spatialValue_smooth he).differentiable (by simp) y.2).hasFDerivAt.comp y
    (ContinuousLinearMap.snd ℝ ℝ Space).hasFDerivAt
  rw [hv]
  change fderiv ℝ (spatialValue e ∘ Prod.snd) y (spaceTimeDirection j.succ) = _
  rw [hd.fderiv]
  rfl

def suspensionCode (e : FieldExpr) : VelocityExpr :=
  letI := ShearFlows.neZeroFour
  ![e.diff 2, .mul (.const (-1)) (e.diff 1), unitSpatialClockExpr]

theorem suspensionCode_valid {e : FieldExpr} (he : e.Valid) : (suspensionCode e).Valid := by
  intro j
  fin_cases j
  · exact FieldExpr.valid_diff he 2
  · exact ⟨trivial, FieldExpr.valid_diff he 1⟩
  · exact unitSpatialClockExpr_valid

theorem suspensionCode_noTime {e : FieldExpr} (ht : NoTime e) (j : Fin 3) :
    NoTime (suspensionCode e j) := by
  fin_cases j
  · exact noTime_diff ht 2
  · exact ⟨trivial, noTime_diff ht 1⟩
  · change (1 : Fin 4) ≠ 0 ∧ (2 : Fin 4) ≠ 0
    decide

noncomputable def suspensionField (e : FieldExpr) (x : Space) : Space :=
  letI := ShearFlows.neZeroThree
  ![scalarD 1 (spatialValue e) x, -scalarD 0 (spatialValue e) x,
    unitSpatialClock (horizontal x)]

theorem suspensionCode_val {e : FieldExpr} (he : e.Valid) (ht : NoTime e) :
    (suspensionCode e).val = fun y => suspensionField e y.2 := by
  funext y j
  fin_cases j
  · exact spatialValue_diff he ht 1 y
  · change ((-1 : ℚ) : ℝ) * (e.diff 1).val y = -scalarD 0 (spatialValue e) y.2
    norm_num only [Rat.cast_neg, Rat.cast_one, neg_one_mul]
    exact congrArg Neg.neg (spatialValue_diff he ht 0 y)
  · exact unitSpatialClockExpr_val y

theorem suspensionField_eq (e : FieldExpr) :
    suspensionField e = potentialSuspension (spatialValue e) (fun _ => 0) + verticalClock := by
  funext x j
  fin_cases j <;> simp [suspensionField, potentialSuspension, verticalClock, scalarD, basis]

theorem suspensionField_smooth {e : FieldExpr} (he : e.Valid) :
    ContDiff ℝ ∞ (suspensionField e) := by
  rw [suspensionField_eq]
  exact (potentialSuspension_smooth (spatialValue_smooth he) contDiff_const).add verticalClock_smooth

theorem suspensionField_divergence {e : FieldExpr} (he : e.Valid) (x : Space) :
    divergence (suspensionField e) x = 0 := by
  have hs := potentialSuspension_smooth (spatialValue_smooth he)
    (show ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ)) from contDiff_const)
  have hz : scalarD 2 (fun _ : Space => (0 : ℝ)) = 0 := by
    funext y
    simp [scalarD]
  have hd := potentialSuspension_divergence (spatialValue_smooth he) contDiff_const hz x
  rw [suspensionField_eq]
  unfold divergence derivative
  simp_rw [fderiv_add (hs.differentiable (by simp) x)
    (verticalClock_smooth.differentiable (by simp) x), add_apply, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  change divergence (potentialSuspension (spatialValue e) (fun _ => 0)) x +
    divergence verticalClock x = 0
  rw [hd, verticalClock_divergence, add_zero]

theorem suspensionField_mean_zero {e : FieldExpr} (he : e.Valid)
    (hp : CubePeriodic 1 (spatialValue e)) :
    (∫ x in fundamentalCube 1, suspensionField e x) = 0 := by
  have hs := potentialSuspension_smooth (spatialValue_smooth he)
    (show ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ)) from contDiff_const)
  rw [suspensionField_eq]
  change (∫ x in fundamentalCube 1,
    potentialSuspension (spatialValue e) (fun _ => 0) x + verticalClock x) = 0
  have hi : IntegrableOn (potentialSuspension (spatialValue e) (fun _ => 0)) (fundamentalCube 1) :=
    hs.continuous.integrableOn_Icc
  have hj : IntegrableOn verticalClock (fundamentalCube 1) := verticalClock_smooth.continuous.integrableOn_Icc
  rw [integral_add hi hj,
    potentialSuspension_mean_zero (by norm_num : (0 : ℝ) ≤ 1)
      (spatialValue_smooth he) contDiff_const hp (fun _ _ => rfl),
    verticalClock_mean_zero, add_zero]

theorem suspensionField_periodic {e : FieldExpr} (he : e.Valid)
    (hp : CubePeriodic 1 (spatialValue e)) : CubePeriodic 1 (suspensionField e) := by
  have hH := potentialSuspension_periodic (spatialValue_smooth he)
    (show ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ)) from contDiff_const) hp (fun _ _ => rfl)
  have hV : CubePeriodic 1 verticalClock := by
    intro x n
    have hh : horizontal (x + latticeVector 1 n) =
        horizontal x + fun j => (n j.castSucc : ℝ) := by
      ext j
      fin_cases j <;> simp [horizontal, latticeVector]
    simp only [verticalClock, hh, unitSpatialClock_periodic]
  intro x n
  rw [suspensionField_eq]
  exact congrArg₂ (· + ·) (hH x n) (hV x n)

end SpatialExpression
end ForcedComputation

end OAI
