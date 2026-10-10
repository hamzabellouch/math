import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedFieldBalls

namespace OAI

/-! Certified evaluation of a flat smooth atom at an approximate real
argument. A global derivative bound controls the argument error. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set Filter
open scoped ContDiff Topology

def profileNoCoord : ProfileExpr → Prop
  | .coord => False
  | .const _ | .glue _ _ _ | .denom _ _ _ => True
  | .add p q | .mul p q => profileNoCoord p ∧ profileNoCoord q

theorem profileNoCoord_bound {p : ProfileExpr} (hp : profileNoCoord p) (x : ℝ) :
    |p.val x| ≤ (p.bound 0 : ℝ) := by
  induction p with
  | const r => simp [ProfileExpr.val, ProfileExpr.bound]
  | coord => exact False.elim hp
  | glue k a b => simpa [ProfileExpr.val, ProfileExpr.bound] using
      gluePower_bound k ((a : ℝ) * x + b)
  | denom k a b => simpa [ProfileExpr.val, ProfileExpr.bound] using
      denomPower_bound k ((a : ℝ) * x + b)
  | add p q ihp ihq =>
    simpa only [ProfileExpr.val, ProfileExpr.bound, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add (ihp hp.1) (ihq hp.2))
  | mul p q ihp ihq =>
    simpa only [ProfileExpr.val, ProfileExpr.bound, Rat.cast_mul, abs_mul] using
      mul_le_mul (ihp hp.1) (ihq hp.2) (abs_nonneg _)
        (Rat.cast_nonneg.mpr (p.bound_nonneg 0))

def SmoothAtom.derivativeBound (a : SmoothAtom) : ℚ := a.profile.diff.bound 0

theorem SmoothAtom.lipschitz_bound (a : SmoothAtom) (x y : ℝ) :
    |a.profile.val x - a.profile.val y| ≤ (a.derivativeBound : ℝ) * |x - y| := by
  have hnc : profileNoCoord a.profile.diff := by
    cases a <;> simp [SmoothAtom.profile, ProfileExpr.diff, ProfileExpr.sub, profileNoCoord]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (a.profile.hasDerivAt z).hasDerivWithinAt)
    (fun z _ => show ‖a.profile.diff.val z‖ ≤ (a.derivativeBound : ℝ) by
      simpa only [Real.norm_eq_abs, SmoothAtom.derivativeBound] using profileNoCoord_bound hnc z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using h

namespace ProfileEvaluation

def Ready (p : ProfileExpr) (q ε : ℚ) (n : ℕ) : Prop := (p.enclose q n).radius ≤ ε

instance (p : ProfileExpr) (q ε : ℚ) (n : ℕ) : Decidable (Ready p q ε n) :=
  inferInstanceAs (Decidable ((p.enclose q n).radius ≤ ε))

theorem ready_exists (p : ProfileExpr) (q : ℚ) {ε : ℚ} (hε : 0 < ε) :
    ∃ n, Ready p q ε n := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := ((p.enclose_converges q).2.eventually_lt_const he).exists
  exact ⟨n, by exact_mod_cast hn.le⟩

def evaluate (p : ProfileExpr) (q ε : ℚ) (hε : 0 < ε) : ℚ :=
  (p.enclose q (Nat.find (ready_exists p q hε))).center

theorem evaluate_spec (p : ProfileExpr) (q ε : ℚ) (hε : 0 < ε) :
    |p.val q - (evaluate p q ε hε : ℝ)| ≤ (ε : ℝ) := by
  have h := p.enclose_contains q (Nat.find (ready_exists p q hε))
  exact h.trans (by exact_mod_cast Nat.find_spec (ready_exists p q hε))

end ProfileEvaluation

def SmoothAtom.enclose (a : SmoothAtom) (b : QBall) (n : ℕ) : QBall :=
  ⟨ProfileEvaluation.evaluate a.profile b.center (ClockedExpr.dyadic n)
      (ClockedExpr.dyadic_pos n),
    ClockedExpr.dyadic n + a.derivativeBound * b.radius⟩

theorem SmoothAtom.enclose_contains (a : SmoothAtom) {b : QBall} {x : ℝ}
    (hb : b.Contains x) (n : ℕ) : (a.enclose b n).Contains (a.profile.val x) := by
  have he := ProfileEvaluation.evaluate_spec a.profile b.center
    (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n)
  have hl := (a.lipschitz_bound x b.center).trans
    (mul_le_mul_of_nonneg_left hb (Rat.cast_nonneg.mpr (a.profile.diff.bound_nonneg 0)))
  change |a.profile.val x - _| ≤ _
  calc
    _ ≤ |a.profile.val x - a.profile.val b.center| + |a.profile.val b.center - _| := abs_sub_le _ _ _
    _ ≤ (a.derivativeBound : ℝ) * b.radius + (ClockedExpr.dyadic n : ℝ) := add_le_add hl he
    _ = _ := by
      dsimp only [SmoothAtom.enclose]
      push_cast
      ring

theorem SmoothAtom.enclose_converges (a : SmoothAtom) {b : ℕ → QBall} {x : ℝ}
    (hb : ∀ n, (b n).Contains x) (hr : QBall.Converges b x) :
    QBall.Converges (fun n => a.enclose (b n) n) (a.profile.val x) := by
  apply QBall.converges_of_contains (fun n => a.enclose_contains (hb n) n)
  have h := ClockedExpr.dyadic_tendsto.add (hr.2.const_mul (a.derivativeBound : ℝ))
  simpa only [SmoothAtom.enclose, Rat.cast_add, Rat.cast_mul, mul_zero, add_zero] using h

end ForcedComputation

end

end OAI
