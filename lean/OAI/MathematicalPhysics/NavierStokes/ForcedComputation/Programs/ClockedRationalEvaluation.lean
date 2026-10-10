import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedFieldBalls

namespace OAI

/-! Finite rational evaluation of a clocked expression, with an adaptive
search justified by convergence of its explicit rational enclosures. -/

namespace ForcedComputation.ClockedExpr
open ShearFlows Filter
open scoped Topology

noncomputable def enclose : (e : ClockedExpr) → e.Valid → RationalSpaceTime → ℕ → QBall
  | .const r, _, _, _ => .exact r
  | .profile q, _, y, n => q.enclose y.1 n
  | .field q e, he, y, n => fieldBall q e he y n
  | .add e f, he, y, n => (e.enclose he.1 y n).add (f.enclose he.2 y n)
  | .mul e f, he, y, n => (e.enclose he.1 y n).mul (f.enclose he.2 y n)

theorem enclose_contains {e : ClockedExpr} (he : e.Valid) (y : RationalSpaceTime) (n : ℕ) :
    (e.enclose he y n).Contains (e.val (rationalPoint y)) := by
  induction e with
  | const r => exact QBall.contains_exact r
  | profile q => exact q.enclose_contains y.1 n
  | field q e => exact fieldBall_contains q he y n
  | add e f ih₁ ih₂ => exact QBall.contains_add (ih₁ he.1) (ih₂ he.2)
  | mul e f ih₁ ih₂ => exact QBall.contains_mul (ih₁ he.1) (ih₂ he.2)

theorem enclose_converges {e : ClockedExpr} (he : e.Valid) (y : RationalSpaceTime) :
    QBall.Converges (e.enclose he y) (e.val (rationalPoint y)) := by
  induction e with
  | const r => exact QBall.converges_exact r
  | profile q => exact q.enclose_converges y.1
  | field q e => exact fieldBall_converges q he y
  | add e f ih₁ ih₂ => exact (ih₁ he.1).add (ih₂ he.2)
  | mul e f ih₁ ih₂ => exact (ih₁ he.1).mul (ih₂ he.2)

noncomputable def Ready (e : ClockedExpr) (he : e.Valid) (y : RationalSpaceTime)
    (ε : ℚ) (n : ℕ) : Prop := (e.enclose he y n).radius ≤ ε

noncomputable instance (e : ClockedExpr) (he : e.Valid) (y : RationalSpaceTime)
    (ε : ℚ) (n : ℕ) : Decidable (e.Ready he y ε n) :=
  inferInstanceAs (Decidable ((e.enclose he y n).radius ≤ ε))

theorem ready_exists {e : ClockedExpr} (he : e.Valid) (y : RationalSpaceTime)
    {ε : ℚ} (hε : 0 < ε) : ∃ n, e.Ready he y ε n := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := ((e.enclose_converges he y).2.eventually_lt_const hε').exists
  exact ⟨n, by exact_mod_cast hn.le⟩

noncomputable def evaluateRational (e : ClockedExpr) (he : e.Valid)
    (y : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  (e.enclose he y (Nat.find (e.ready_exists he y hε))).center

theorem evaluateRational_spec {e : ClockedExpr} (he : e.Valid)
    (y : RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) :
    |e.val (rationalPoint y) - (e.evaluateRational he y ε hε : ℝ)| ≤ (ε : ℝ) := by
  have h := e.enclose_contains he y (Nat.find (e.ready_exists he y hε))
  exact h.trans (by exact_mod_cast Nat.find_spec (e.ready_exists he y hε))

end ForcedComputation.ClockedExpr

end OAI
