import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FastVectorArithmetic

namespace OAI

/-! Terminating rational-ball searches give product names and the scaled
physical-time input used by the viscosity-dependent detector evaluator. -/

namespace ForcedComputation
open ShearFlows Filter
open scoped Topology

def scalarBallReady (b : ℕ → QBall) (ε : ℚ) (n : ℕ) : Prop := (b n).radius ≤ ε

instance (b : ℕ → QBall) (ε : ℚ) (n : ℕ) : Decidable (scalarBallReady b ε n) :=
  inferInstanceAs (Decidable ((b n).radius ≤ ε))

theorem scalarBallReady_exists {b : ℕ → QBall} {x : ℝ}
    (hb : QBall.Converges b x) {ε : ℚ} (hε : 0 < ε) :
    ∃ n, scalarBallReady b ε n := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := (hb.2.eventually_lt_const he).exists
  exact ⟨n, by exact_mod_cast hn.le⟩

def scalarBallApprox (b : ℕ → QBall) (ε : ℚ)
    (h : ∃ n, scalarBallReady b ε n) : ℚ := (b (Nat.find h)).center

theorem scalarBallApprox_spec {b : ℕ → QBall} {x : ℝ}
    (hb : QBall.Converges b x) (hc : ∀ n, (b n).Contains x)
    (ε : ℚ) (hε : 0 < ε) :
    |x - (scalarBallApprox b ε (scalarBallReady_exists hb hε) : ℝ)| ≤ (ε : ℝ) := by
  exact (hc _).trans (by exact_mod_cast Nat.find_spec (scalarBallReady_exists hb hε))

def mulNameBalls (a b : ℕ → ℚ) (n : ℕ) : QBall :=
  (realNameBall a n).mul (realNameBall b n)

theorem mulNameBalls_contains {a b : ℕ → ℚ} {x y : ℝ}
    (ha : IsFastRealName a x) (hb : IsFastRealName b y) (n : ℕ) :
    (mulNameBalls a b n).Contains (x * y) :=
  QBall.contains_mul (realNameBall_contains ha n) (realNameBall_contains hb n)

theorem mulNameBalls_converges {a b : ℕ → ℚ} {x y : ℝ}
    (ha : IsFastRealName a x) (hb : IsFastRealName b y) :
    QBall.Converges (mulNameBalls a b) (x * y) :=
  (realNameBall_converges ha).mul (realNameBall_converges hb)

def mulFastName {x y : ℝ} (a b : ℕ → ℚ)
    (ha : IsFastRealName a x) (hb : IsFastRealName b y) : ℕ → ℚ := fun n =>
  scalarBallApprox (mulNameBalls a b) ((2 : ℚ) ^ (-(n : ℤ)))
    (scalarBallReady_exists (mulNameBalls_converges ha hb) (by positivity))

theorem mulFastName_spec {x y : ℝ} (a b : ℕ → ℚ)
    (ha : IsFastRealName a x) (hb : IsFastRealName b y) :
    IsFastRealName (mulFastName a b ha hb) (x * y) := by
  intro n
  have h := scalarBallApprox_spec (mulNameBalls_converges ha hb)
    (mulNameBalls_contains ha hb) ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)
  simpa [mulFastName, errorTolerance] using h

def timeName (b : ℕ → RationalSpaceTime) : ℕ → ℚ := fun n => (b n).1

theorem timeName_spec {b : ℕ → RationalSpaceTime} {z : SpaceTime}
    (hb : IsFastName b z) : IsFastRealName (timeName b) z.1 := by
  intro n
  have h := (norm_fst_le (z - rationalPoint (b n))).trans (hb n)
  simpa only [timeName, Prod.fst_sub, rationalPoint, Real.norm_eq_abs] using h

def scaleTimeName {ν : ℝ} {z : SpaceTime} (a : ℕ → ℚ)
    (b : ℕ → RationalSpaceTime) (ha : IsFastRealName a ν) (hb : IsFastName b z) :
    ℕ → RationalSpaceTime := fun n =>
  (mulFastName a (timeName b) ha (timeName_spec hb) n, (b n).2)

theorem scaleTimeName_spec {ν : ℝ} {z : SpaceTime} (a : ℕ → ℚ)
    (b : ℕ → RationalSpaceTime) (ha : IsFastRealName a ν) (hb : IsFastName b z) :
    IsFastName (scaleTimeName a b ha hb) (ν * z.1, z.2) := by
  intro n
  apply norm_prod_le_iff.mpr
  exact ⟨mulFastName_spec a (timeName b) ha (timeName_spec hb) n,
    (norm_snd_le (z - rationalPoint (b n))).trans (hb n)⟩

end ForcedComputation

end OAI
