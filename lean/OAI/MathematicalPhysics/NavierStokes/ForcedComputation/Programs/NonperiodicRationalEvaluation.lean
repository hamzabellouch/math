import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicAtoms

namespace OAI

/-! A terminating rational evaluation procedure for every finite moving
gate expression and all of its formal mixed derivatives. -/

noncomputable section
namespace ForcedComputation.NonperiodicExpr
open ShearFlows Filter
open scoped Topology

def enclose : NonperiodicExpr → RationalSpaceTime → ℕ → QBall
  | .const r, _, _ => .exact r
  | .coord j, y, _ => .exact (rationalCoord j y)
  | .atom a e, y, n => a.enclose (e.enclose y n) n
  | .add e f, y, n => (e.enclose y n).add (f.enclose y n)
  | .mul e f, y, n => (e.enclose y n).mul (f.enclose y n)

theorem enclose_contains (e : NonperiodicExpr) (y : RationalSpaceTime) (n : ℕ) :
    (e.enclose y n).Contains (e.val (rationalPoint y)) := by
  induction e with
  | const r => exact QBall.contains_exact r
  | coord j => simpa only [val, enclose, timeSpaceCoord_rational] using
      QBall.contains_exact (rationalCoord j y)
  | atom a e ih => exact a.enclose_contains ih n
  | add e f ihe ihf => exact QBall.contains_add ihe ihf
  | mul e f ihe ihf => exact QBall.contains_mul ihe ihf

theorem enclose_converges (e : NonperiodicExpr) (y : RationalSpaceTime) :
    QBall.Converges (e.enclose y) (e.val (rationalPoint y)) := by
  induction e with
  | const r => exact QBall.converges_exact r
  | coord j => simpa only [val, enclose, timeSpaceCoord_rational] using
      QBall.converges_exact (rationalCoord j y)
  | atom a e ih => exact a.enclose_converges (fun n => e.enclose_contains y n) ih
  | add e f ihe ihf => exact ihe.add ihf
  | mul e f ihe ihf => exact ihe.mul ihf

def Ready (e : NonperiodicExpr) (y : RationalSpaceTime) (ε : ℚ) (n : ℕ) : Prop :=
  (e.enclose y n).radius ≤ ε

instance (e : NonperiodicExpr) (y : RationalSpaceTime) (ε : ℚ) (n : ℕ) :
    Decidable (e.Ready y ε n) := inferInstanceAs (Decidable ((e.enclose y n).radius ≤ ε))

theorem ready_exists (e : NonperiodicExpr) (y : RationalSpaceTime) {ε : ℚ} (hε : 0 < ε) :
    ∃ n, e.Ready y ε n := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := ((e.enclose_converges y).2.eventually_lt_const he).exists
  exact ⟨n, by exact_mod_cast hn.le⟩

def evaluateRational (e : NonperiodicExpr) (y : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  (e.enclose y (Nat.find (e.ready_exists y hε))).center

theorem evaluateRational_spec (e : NonperiodicExpr) (y : RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) :
    |e.val (rationalPoint y) - (e.evaluateRational y ε hε : ℝ)| ≤ (ε : ℝ) := by
  have h := e.enclose_contains y (Nat.find (e.ready_exists y hε))
  exact h.trans (by exact_mod_cast Nat.find_spec (e.ready_exists y hε))

end ForcedComputation.NonperiodicExpr

end

end OAI
