import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedVector

namespace OAI

/-! Finite clocked expressions relative to the given planar-field evaluator.
Input atoms are derivatives of the input field, not derivatives of the
constructed force.  Product and chain rules remain part of the compiler. -/

namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff BigOperators

abbrev PlanarComponents := Fin 2 → SpaceTime → ℝ

noncomputable def componentJet (F : PlanarComponents) (α : List (Fin 4)) (j : Fin 2) :=
  ClockedExpr.scalarMixed (F j) α

theorem componentJet_smooth {F : PlanarComponents}
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (α : List (Fin 4)) (j : Fin 2) :
    ContDiff ℝ ∞ (componentJet F α j) := by
  induction α with
  | nil => exact hF j
  | cons k α ih =>
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The numerical information supplied with the effectively specified
input planar field.  All bounds are global input-derivative bounds. -/
structure PlanarJetOracle (F : PlanarComponents) where
  bound : List (Fin 4) → Fin 2 → ℚ
  bound_nonneg : ∀ α j, 0 ≤ bound α j
  jet_bound : ∀ α j y, |componentJet F α j y| ≤ (bound α j : ℝ)
  enclose : List (Fin 4) → Fin 2 → RationalSpaceTime → ℕ → QBall
  enclose_contains : ∀ α j q n, (enclose α j q n).Contains
    (componentJet F α j (rationalPoint q))
  enclose_converges : ∀ α j q, QBall.Converges (enclose α j q)
    (componentJet F α j (rationalPoint q))

inductive DetectorExpr
  | known (e : ClockedExpr)
  | input (q : ProfileExpr) (α : List (Fin 4)) (j : Fin 2)
  | add (e f : DetectorExpr)
  | mul (e f : DetectorExpr)
  deriving DecidableEq

namespace DetectorExpr

noncomputable def val (F : PlanarComponents) : DetectorExpr → SpaceTime → ℝ
  | .known e, y => e.val y
  | .input q α j, y => componentJet F α j (clockedPoint q y)
  | .add e f, y => e.val F y + f.val F y
  | .mul e f, y => e.val F y * f.val F y

def Valid : DetectorExpr → Prop
  | .known e => e.Valid
  | .input _ _ _ => True
  | .add e f => e.Valid ∧ f.Valid
  | .mul e f => e.Valid ∧ f.Valid

def diff (k : Fin 4) : DetectorExpr → DetectorExpr
  | .known e => .known (e.diff k)
  | .input q α j => if k = 0 then
      .mul (.known (.profile q.diff)) (.input q (0 :: α) j)
    else .input q (k :: α) j
  | .add e f => .add (e.diff k) (f.diff k)
  | .mul e f => .add (.mul (e.diff k) f) (.mul e (f.diff k))

theorem valid_diff {e : DetectorExpr} (he : e.Valid) (k : Fin 4) :
    (e.diff k).Valid := by
  induction e with
  | known e => exact e.valid_diff he k
  | input q α j => simp only [diff]; split_ifs <;> trivial
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩
  | mul e f ihe ihf => exact ⟨⟨ihe he.1, he.2⟩, ⟨he.1, ihf he.2⟩⟩

theorem smooth {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) : ContDiff ℝ ∞ (e.val F) := by
  induction e with
  | known e => exact e.smooth he
  | input q α j => exact (componentJet_smooth hF α j).comp (clockedPoint_smooth q)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)
  | mul e f ihe ihf => exact (ihe he.1).mul (ihf he.2)

theorem val_diff {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (k : Fin 4) (y : SpaceTime) :
    (e.diff k).val F y = fderiv ℝ (e.val F) y (spaceTimeDirection k) := by
  induction e with
  | known e => exact e.val_diff he k y
  | input q α j =>
    have hd := ((componentJet_smooth hF α j).differentiable (by simp)
      (clockedPoint q y)).hasFDerivAt.comp y
        ((clockedPoint_smooth q).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (componentJet F α j ∘ clockedPoint q) y (spaceTimeDirection k)
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, clockedPoint_direction]
    by_cases hk : k = 0
    · subst k
      simp only [diff, ite_true, val, ClockedExpr.val, map_smul, smul_eq_mul]
      rfl
    · simp only [diff, hk, ite_false, val]
      rfl
  | add e f ihe ihf =>
    rw [show val F (.add e f) = e.val F + f.val F from rfl,
      fderiv_add ((smooth hF he.1).differentiable (by simp) y)
        ((smooth hF he.2).differentiable (by simp) y)]
    exact congrArg₂ (· + ·) (ihe he.1) (ihf he.2)
  | mul e f ihe ihf =>
    have hd := ((smooth hF he.1).differentiable (by simp) y).hasFDerivAt.mul
      ((smooth hF he.2).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (e.val F * f.val F) y (spaceTimeDirection k)
    rw [hd.fderiv]
    simp only [diff, val, add_apply, smul_apply, smul_eq_mul]
    rw [ihe he.1, ihf he.2]
    ring

def diffWord (e : DetectorExpr) : List (Fin 4) → DetectorExpr
  | [] => e
  | k :: α => (e.diffWord α).diff k

theorem valid_diffWord {e : DetectorExpr} (he : e.Valid) (α : List (Fin 4)) :
    (e.diffWord α).Valid := by
  induction α with
  | nil => exact he
  | cons k α ih => exact valid_diff ih k

theorem val_diffWord {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {e : DetectorExpr} (he : e.Valid) (α : List (Fin 4)) :
    (e.diffWord α).val F = ClockedExpr.scalarMixed (e.val F) α := by
  induction α with
  | nil => rfl
  | cons k α ih =>
    funext y
    change ((e.diffWord α).diff k).val F y = _
    rw [val_diff hF (valid_diffWord he α), ih]
    rfl

def bound {F : PlanarComponents} (o : PlanarJetOracle F) (M : ℚ) : DetectorExpr → ℚ
  | .known e => e.bound M
  | .input _ α j => o.bound α j
  | .add e f => e.bound o M + f.bound o M
  | .mul e f => e.bound o M * f.bound o M

theorem bound_nonneg {F : PlanarComponents} (o : PlanarJetOracle F)
    (M : ℚ) (e : DetectorExpr) : 0 ≤ e.bound o M := by
  induction e with
  | known e => exact e.bound_nonneg M
  | input q α j => exact o.bound_nonneg α j
  | add e f ihe ihf => exact add_nonneg ihe ihf
  | mul e f ihe ihf => exact mul_nonneg ihe ihf

theorem val_bound {F : PlanarComponents} (o : PlanarJetOracle F)
    {e : DetectorExpr} (he : e.Valid) (M : ℚ) (y : SpaceTime)
    (hy : |y.1| ≤ |(M : ℝ)|) : |e.val F y| ≤ (e.bound o M : ℝ) := by
  induction e with
  | known e => exact e.val_bound he M y hy
  | input q α j => exact o.jet_bound α j _
  | add e f ihe ihf =>
    simpa only [val, bound, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add (ihe he.1) (ihf he.2))
  | mul e f ihe ihf =>
    simpa only [val, bound, Rat.cast_mul, abs_mul] using
      mul_le_mul (ihe he.1) (ihf he.2) (abs_nonneg _)
        (Rat.cast_nonneg.mpr (e.bound_nonneg o M))

end DetectorExpr
end ForcedComputation.VelocityDetector

end OAI
