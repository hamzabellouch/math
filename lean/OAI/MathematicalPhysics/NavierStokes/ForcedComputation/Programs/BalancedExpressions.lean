import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicForceEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulseExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift

namespace OAI

/-! The balanced compiler uses the existing nonperiodic finite syntax.
Periodic time pulses are replaced, on a rational time window, by the finite
set of translates which can meet that window. Spatial cutoffs remain exact
on the whole plane, including their collars. -/

noncomputable section
namespace ForcedComputation.BalancedExpressions
open ShearFlows PlanarHamiltonian VelocityDetector Set
open scoped ContDiff BigOperators

def coordinate (j : Fin 2) : NonperiodicExpr := .coord j.castSucc.succ

theorem coordinate_val (j : Fin 2) (y : SpaceTime) :
    (coordinate j).val y = horizontal y.2 j := by
  fin_cases j <;> rfl

def cutoffCode (R : RationalBox 2) (δ : ℚ) : NonperiodicExpr :=
  .mul (NonperiodicExpr.composeProfile (.cutoff (R.lower 0-2*δ) (R.lower 0-δ)
    (R.upper 0+δ) (R.upper 0+2*δ)) (coordinate 0))
    (NonperiodicExpr.composeProfile (.cutoff (R.lower 1-2*δ) (R.lower 1-δ)
      (R.upper 1+δ) (R.upper 1+2*δ)) (coordinate 1))

theorem cutoffCode_val (R : RationalBox 2) (δ : ℚ) (y : SpaceTime) :
    (cutoffCode R δ).val y = rectangleCutoff R δ (horizontal y.2) := by
  simp only [cutoffCode, NonperiodicExpr.val, NonperiodicExpr.val_composeProfile,
    ProfileExpr.val_cutoff, coordinate_val, rectangleCutoff, Rat.cast_sub,
    Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

def primitiveCode : Primitive → NonperiodicExpr
  | .translation v => .sub (.mul (.const (v 0)) (coordinate 1))
      (.mul (.const (v 1)) (coordinate 0))
  | .horizontal c a => .mul (.const (a/2))
      (.mul (.sub (coordinate 1) (.const (c 1))) (.sub (coordinate 1) (.const (c 1))))
  | .vertical c a => .mul (.const (-a/2))
      (.mul (.sub (coordinate 0) (.const (c 0))) (.sub (coordinate 0) (.const (c 0))))

theorem primitiveCode_val (p : Primitive) (y : SpaceTime) :
    (primitiveCode p).val y = p.potential (horizontal y.2) := by
  cases p <;> simp only [primitiveCode, Primitive.potential, NonperiodicExpr.sub,
    NonperiodicExpr.val, coordinate_val, translationPotential, horizontalPotential,
    verticalPotential, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] <;> ring

def potentialCode (p : Pulse) : NonperiodicExpr :=
  .mul (cutoffCode p.rectangle p.collar) (primitiveCode p.primitive)

theorem potentialCode_val (p : Pulse) (y : SpaceTime) :
    (potentialCode p).val y = p.hamiltonian (horizontal y.2) := by
  rw [potentialCode, NonperiodicExpr.val, cutoffCode_val, primitiveCode_val]
  rfl

def translateIndices (p : Pulse) (u v : ℚ) : Finset ℤ :=
  Finset.Icc ⌊u-p.finish⌋ ⌈v-p.start⌉

def translatePulse (p : Pulse) (k : ℤ) : NonperiodicExpr :=
  NonperiodicExpr.composeProfile (ProfileExpr.ramp p.start p.finish).diff
    (.sub (.coord 0) (.const k))

theorem translatePulse_val (p : Pulse) (k : ℤ) (y : SpaceTime) :
    (translatePulse p k).val y = smoothPulse p.start p.finish (y.1-k) := by
  simp only [translatePulse, NonperiodicExpr.val_composeProfile, NonperiodicExpr.sub,
    NonperiodicExpr.val, ProfileExpr.val_diff, ProfileExpr.val_ramp,
    timeSpaceCoord, Rat.cast_intCast, Rat.cast_neg, Rat.cast_one, neg_one_mul]
  rfl

def pulseCode (p : Pulse) (u v : ℚ) : NonperiodicExpr :=
  NonperiodicExpr.sum ((translateIndices p u v).sort (· ≤ ·) |>.map (translatePulse p))

theorem pulseCode_val {p : Pulse} (hp : p.Valid) (u v : ℚ) {y : SpaceTime}
    (hy : y.1 ∈ Icc (u : ℝ) v) :
    (pulseCode p u v).val y = (PeriodicExpr.intervalPulse p.start p.finish).val y.1 := by
  rw [pulseCode, NonperiodicExpr.sum_val, List.map_map]
  change (((translateIndices p u v).sort (· ≤ ·)).map
    (fun k => (translatePulse p k).val y)).sum = _
  rw [((Finset.sort_perm_toList (translateIndices p u v) (· ≤ ·)).map
    (fun k => (translatePulse p k).val y)).sum_eq, Finset.sum_map_toList]
  have hs : Function.support (smoothPulse (p.start : ℝ) p.finish) ⊆
      Icc (p.start : ℝ) p.finish :=
    (smoothPulse_support (by exact_mod_cast hp.2)).trans Ioo_subset_Icc_self
  have h := periodize_eq_finite (by norm_num : (0 : ℝ) < 1) hs hy
  simpa only [translatePulse_val, PeriodicExpr.val, PeriodicExpr.intervalPulse, Rat.cast_one,
    ProfileExpr.val_diff, ProfileExpr.val_ramp, smoothPulse, one_mul, div_one, translateIndices,
    ← Rat.cast_sub, Rat.floor_cast, Rat.ceil_cast] using h.symm

def hamiltonianCode {n : ℕ} (p : Fin n → Pulse) (u v : ℚ) : NonperiodicExpr :=
  NonperiodicExpr.sum (List.ofFn fun i => .mul (pulseCode (p i) u v) (potentialCode (p i)))

theorem hamiltonianCode_val {n : ℕ} {p : Fin n → Pulse} (hp : ∀ i, (p i).Valid)
    (u v : ℚ) {y : SpaceTime} (hy : y.1 ∈ Icc (u : ℝ) v) :
    (hamiltonianCode p u v).val y = periodicHamiltonian p y.1 (horizontal y.2) := by
  rw [hamiltonianCode, NonperiodicExpr.sum_ofFn_val]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg₂ (· * ·) (pulseCode_val (hp i) u v hy) (potentialCode_val (p i) y)

def hamiltonianField (e : NonperiodicExpr) : NonperiodicVector :=
  ![e.diff 2, .mul (.const (-1)) (e.diff 1), .const 0]

private theorem horizontal_derivative {e : NonperiodicExpr} {H : Plane → ℝ}
    {t : ℝ} (hH : ContDiff ℝ ∞ H)
    (he : ∀ x : Space, e.val (t,x) = H (horizontal x)) (j : Fin 2) (x : Space) :
    (e.diff j.castSucc.succ).val (t,x) = spatialD j H (horizontal x) := by
  have hs : (fun z : Space => e.val (t,z)) = H ∘ horizontalLinear := by
    funext z
    simpa only [Function.comp_apply, horizontalLinear_eq] using he z
  have heq : fderiv ℝ (fun z : Space => e.val (t,z)) x (ShearFlows.basis j.castSucc) =
      fderiv ℝ e.val (t,x) (spaceTimeDirection j.castSucc.succ) := by
    have hf := (e.smooth.differentiable (by simp) (t,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id x))
    have hff : fderiv ℝ (fun z : Space => e.val (t,z)) x =
        (fderiv ℝ e.val (t,x)).comp
          ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) := hf.fderiv
    rw [hff]
    rfl
  rw [e.val_diff, ← heq, hs]
  rw [fderiv_comp x (hH.differentiable (by simp) _) horizontalLinear.differentiableAt,
    horizontalLinear.fderiv]
  change fderiv ℝ H (horizontalLinear x) (horizontalLinear (ShearFlows.basis j.castSucc)) = _
  rw [VelocityDetector.horizontalLinear_basis, horizontalLinear_eq]
  rfl

theorem hamiltonianField_val {e : NonperiodicExpr} {H : Plane → ℝ} {t : ℝ}
    (hH : ContDiff ℝ ∞ H) (he : ∀ x : Space, e.val (t,x) = H (horizontal x)) (x : Space) :
    (hamiltonianField e).val (t,x) = planeInclusion (field H (horizontal x)) := by
  have h₀ := horizontal_derivative hH he 0 x
  have h₁ := horizontal_derivative hH he 1 x
  ext j
  fin_cases j
  · simpa [hamiltonianField, NonperiodicVector.val, planeInclusion, field,
      PlanarHamiltonian.basis] using h₁
  · simpa [hamiltonianField, NonperiodicVector.val, planeInclusion, field,
      PlanarHamiltonian.basis, NonperiodicExpr.val] using congrArg Neg.neg h₀
  · simp [hamiltonianField, NonperiodicVector.val, planeInclusion, field,
      PlanarHamiltonian.basis, NonperiodicExpr.val]

end ForcedComputation.BalancedExpressions

end

end OAI
