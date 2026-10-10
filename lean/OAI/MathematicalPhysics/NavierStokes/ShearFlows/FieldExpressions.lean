import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicExpressions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology


open Set Filter
open scoped BigOperators Topology ContDiff
namespace ShearFlows

noncomputable def timeSpaceCoord (j : Fin 4) : SpaceTime →L[ℝ] ℝ :=
  Fin.cases (ContinuousLinearMap.fst ℝ ℝ Space)
    (fun k => (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℝ ℝ Space)) j

theorem timeSpaceCoord_direction (i j : Fin 4) :
    timeSpaceCoord i (spaceTimeDirection j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

def rationalCoord (j : Fin 4) (q : ℚ × (Fin 3 → ℚ)) : ℚ :=
  Fin.cases q.1 (fun k => q.2 k) j

theorem timeSpaceCoord_rational (j : Fin 4) (q : ℚ × (Fin 3 → ℚ)) :
    timeSpaceCoord j (rationalPoint q) = (rationalCoord j q : ℝ) := by
  fin_cases j <;> rfl

inductive FieldExpr
  | const (q : ℚ)
  | atom (j : Fin 4) (p : PeriodicExpr)
  | add (f g : FieldExpr)
  | mul (f g : FieldExpr)
  deriving DecidableEq

namespace FieldExpr

noncomputable def val : FieldExpr → SpaceTime → ℝ
  | .const q, _ => q
  | .atom j p, y => p.val (timeSpaceCoord j y)
  | .add f g, y => f.val y + g.val y
  | .mul f g, y => f.val y * g.val y

def Valid : FieldExpr → Prop
  | .const _ => True
  | .atom _ p => p.Valid
  | .add f g => f.Valid ∧ g.Valid
  | .mul f g => f.Valid ∧ g.Valid

def diff (j : Fin 4) : FieldExpr → FieldExpr
  | .const _ => .const 0
  | .atom i p => if i = j then .atom i p.diff else .const 0
  | .add f g => .add (f.diff j) (g.diff j)
  | .mul f g => .add (.mul (f.diff j) g) (.mul f (g.diff j))

theorem valid_diff {e : FieldExpr} (he : e.Valid) (j : Fin 4) : (e.diff j).Valid := by
  induction e with
  | const q => trivial
  | atom i p => by_cases hij : i = j <;> simp [diff,hij,Valid] at *; exact p.valid_diff he
  | add f g hf hg => exact ⟨hf he.1,hg he.2⟩
  | mul f g hf hg => exact ⟨⟨hf he.1,he.2⟩,⟨he.1,hg he.2⟩⟩

theorem smooth {e : FieldExpr} (he : e.Valid) : ContDiff ℝ ∞ e.val := by
  induction e with
  | const q => exact contDiff_const
  | atom j p => exact (p.smooth he).comp (timeSpaceCoord j).contDiff
  | add f g hf hg => exact (hf he.1).add (hg he.2)
  | mul f g hf hg => exact (hf he.1).mul (hg he.2)

theorem val_diff {e : FieldExpr} (he : e.Valid) (j : Fin 4) (y : SpaceTime) :
    (e.diff j).val y = fderiv ℝ e.val y (spaceTimeDirection j) := by
  induction e with
  | const q => simp [diff,val]
  | atom i p =>
    have h := (p.hasDerivAt he (timeSpaceCoord i y)).hasFDerivAt.comp y
      (timeSpaceCoord i).hasFDerivAt
    change _ = fderiv ℝ (p.val ∘ timeSpaceCoord i) y (spaceTimeDirection j)
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, timeSpaceCoord_direction]
    by_cases hij : i=j <;> simp [diff,hij,val]
  | add f g hf hg =>
    have h := ((smooth he.1).differentiable (by simp) y).hasFDerivAt.add
      (((smooth he.2).differentiable (by simp) y).hasFDerivAt)
    change _ = fderiv ℝ (f.val + g.val) y (spaceTimeDirection j)
    rw [h.fderiv]
    exact congrArg₂ (·+·) (hf he.1) (hg he.2)
  | mul f g hf hg =>
    have h := ((smooth he.1).differentiable (by simp) y).hasFDerivAt.mul
      (((smooth he.2).differentiable (by simp) y).hasFDerivAt)
    change _ = fderiv ℝ (f.val * g.val) y (spaceTimeDirection j)
    rw [h.fderiv]
    simp only [diff,val,add_apply,smul_apply,smul_eq_mul]
    rw [hf he.1,hg he.2]
    ring

def diffWord (e : FieldExpr) : List (Fin 4) → FieldExpr :=
  List.rec e (fun j _ acc => acc.diff j)

theorem valid_diffWord {e : FieldExpr} (he : e.Valid) (α : List (Fin 4)) :
    (e.diffWord α).Valid := by
  induction α with
  | nil => exact he
  | cons j α h => exact valid_diff h j

def enclose : FieldExpr → (ℚ × (Fin 3 → ℚ)) → ℕ → QBall
  | .const q, _, _ => .exact q
  | .atom j p, q, n => p.enclose (rationalCoord j q) n
  | .add f g, q, n => (f.enclose q n).add (g.enclose q n)
  | .mul f g, q, n => (f.enclose q n).mul (g.enclose q n)

theorem enclose_contains {e : FieldExpr} (he : e.Valid) (q : ℚ × (Fin 3 → ℚ)) (n : ℕ) :
    (e.enclose q n).Contains (e.val (rationalPoint q)) := by
  induction e with
  | const r => exact QBall.contains_exact r
  | atom j p => simpa [enclose,val,timeSpaceCoord_rational] using p.enclose_contains he (rationalCoord j q) n
  | add f g hf hg => exact QBall.contains_add (hf he.1) (hg he.2)
  | mul f g hf hg => exact QBall.contains_mul (hf he.1) (hg he.2)

theorem enclose_converges {e : FieldExpr} (he : e.Valid) (q : ℚ × (Fin 3 → ℚ)) :
    QBall.Converges (e.enclose q) (e.val (rationalPoint q)) := by
  induction e with
  | const r => exact QBall.converges_exact r
  | atom j p => simpa [enclose,val,timeSpaceCoord_rational] using p.enclose_converges he (rationalCoord j q)
  | add f g hf hg => exact QBall.Converges.add (hf he.1) (hg he.2)
  | mul f g hf hg => exact QBall.Converges.mul (hf he.1) (hg he.2)

def bound : FieldExpr → ℚ
  | .const q => |q|
  | .atom _ p => p.bound
  | .add f g => f.bound + g.bound
  | .mul f g => f.bound * g.bound

theorem bound_nonneg (e : FieldExpr) : 0 ≤ e.bound := by
  induction e with
  | const q => exact abs_nonneg _
  | atom j p => exact p.bound_nonneg
  | add f g hf hg => exact add_nonneg hf hg
  | mul f g hf hg => exact mul_nonneg hf hg

theorem val_bound {e : FieldExpr} (he : e.Valid) (y : SpaceTime) :
    |e.val y| ≤ (e.bound : ℝ) := by
  induction e with
  | const q => simp [val,bound]
  | atom j p => exact p.val_bound he _
  | add f g hf hg => simpa [val,bound] using (abs_add_le _ _).trans (add_le_add (hf he.1) (hg he.2))
  | mul f g hf hg =>
    simpa [val,bound,abs_mul] using mul_le_mul (hf he.1) (hg he.2) (abs_nonneg _)
      (show (0 : ℝ) ≤ f.bound by exact_mod_cast bound_nonneg f)

def sum (l : List FieldExpr) : FieldExpr := l.foldr .add (.const 0)

theorem val_sum (l : List FieldExpr) (y : SpaceTime) : (sum l).val y = (l.map (fun e => e.val y)).sum := by
  induction l with
  | nil => simp [sum,val]
  | cons a l h =>
      rw [show sum (a :: l) = .add a (sum l) from rfl]
      simp only [val,List.map_cons,List.sum_cons,h]

theorem valid_sum {l : List FieldExpr} (hl : ∀ e ∈ l, e.Valid) : (sum l).Valid := by
  induction l with
  | nil => trivial
  | cons e l h => exact ⟨hl e (by simp),h (fun f hf => hl f (by simp [hf]))⟩

end FieldExpr

abbrev VelocityExpr := Fin 3 → FieldExpr

namespace VelocityExpr

def Valid (c : VelocityExpr) : Prop := ∀ k, (c k).Valid

noncomputable def val (c : VelocityExpr) : Velocity := fun y k => (c k).val y

def diffWord (c : VelocityExpr) (α : List (Fin 4)) : VelocityExpr := fun k => (c k).diffWord α

theorem valid_diffWord {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) :
    (c.diffWord α).Valid := fun k => (c k).valid_diffWord (hc k) α

theorem smooth {c : VelocityExpr} (hc : c.Valid) : ContDiff ℝ ∞ c.val :=
  contDiff_pi.mpr fun k => FieldExpr.smooth (hc k)

theorem val_diffWord {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) :
    (c.diffWord α).val = mixedDerivative c.val α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y k
    rw [mixedDerivative, ← ih]
    have h := fderiv_pi (fun k => (FieldExpr.smooth (FieldExpr.valid_diffWord (hc k) α)).differentiable (by simp) y)
    change ((c k).diffWord (j :: α)).val y =
      (fderiv ℝ (fun y k => ((c k).diffWord α).val y) y (spaceTimeDirection j)) k
    rw [h]
    exact FieldExpr.val_diff (FieldExpr.valid_diffWord (hc k) α) j y

def bound (c : VelocityExpr) (α : List (Fin 4)) : ℕ :=
  ⌈∑ k, ((c k).diffWord α).bound⌉₊

theorem val_bound {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4)) (y : SpaceTime) :
    ‖mixedDerivative c.val α y‖ ≤ (c.bound α : ℝ) := by
  rw [← val_diffWord hc]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
  intro k
  have hb := FieldExpr.val_bound (FieldExpr.valid_diffWord (hc k) α) y
  have hs : ((c k).diffWord α).bound ≤ ∑ j, ((c j).diffWord α).bound :=
    Finset.single_le_sum (fun coordinate _ => FieldExpr.bound_nonneg ((c coordinate).diffWord α))
      (Finset.mem_univ k)
  have hceil : (∑ j, ((c j).diffWord α).bound : ℚ) ≤ ↑(c.bound α) := Nat.le_ceil _
  exact hb.trans (by exact_mod_cast hs.trans hceil)

end VelocityExpr
end ShearFlows

end

end OAI
