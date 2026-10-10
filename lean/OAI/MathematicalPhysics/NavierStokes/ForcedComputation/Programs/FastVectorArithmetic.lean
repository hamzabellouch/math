import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FinitePhaseEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmName

namespace OAI

/-! Finite rational interval arithmetic for vector-valued derivative formulas.
The stopping test is rational and finite; convergence proves its termination. -/

namespace ForcedComputation
open ShearFlows Filter
open scoped Topology

def realNameBall (a : ℕ → ℚ) (n : ℕ) : QBall :=
  ⟨a n, (2 : ℚ) ^ (-(n : ℤ))⟩

def vectorNameBall (a : ℕ → RationalVector) (n : ℕ) (j : Fin 3) : QBall :=
  realNameBall (fun k => a k j) n

theorem realNameBall_contains {a : ℕ → ℚ} {x : ℝ}
    (ha : IsFastRealName a x) (n : ℕ) : (realNameBall a n).Contains x := by
  simpa [realNameBall, QBall.Contains, errorTolerance] using ha n

theorem realNameBall_converges {a : ℕ → ℚ} {x : ℝ}
    (ha : IsFastRealName a x) : QBall.Converges (realNameBall a) x := by
  refine ⟨fastRealName_tendsto ha, ?_⟩
  have he : (fun n => ((realNameBall a n).radius : ℝ)) = errorTolerance := by
    funext n
    simp [realNameBall, errorTolerance]
  rw [he]
  exact errorTolerance_tendsto

theorem vectorNameBall_contains {a : ℕ → RationalVector} {v : Space}
    (ha : IsFastVectorName a v) (n : ℕ) (j : Fin 3) :
    (vectorNameBall a n j).Contains (v j) := by
  apply realNameBall_contains
  intro k
  exact (show |v j - (a k j : ℝ)| ≤ ‖v - rationalVector (a k)‖ from
    norm_le_pi_norm (v - rationalVector (a k)) j).trans (ha k)

theorem vectorNameBall_converges {a : ℕ → RationalVector} {v : Space}
    (ha : IsFastVectorName a v) (j : Fin 3) :
    QBall.Converges (fun n => vectorNameBall a n j) (v j) := by
  apply realNameBall_converges
  intro k
  exact (show |v j - (a k j : ℝ)| ≤ ‖v - rationalVector (a k)‖ from
    norm_le_pi_norm (v - rationalVector (a k)) j).trans (ha k)

def vectorBallReady (b : ℕ → Fin 3 → QBall) (ε : ℚ) (n : ℕ) : Prop :=
  ∀ j, (b n j).radius ≤ ε

instance (b : ℕ → Fin 3 → QBall) (ε : ℚ) (n : ℕ) :
    Decidable (vectorBallReady b ε n) :=
  inferInstanceAs (Decidable (∀ j, (b n j).radius ≤ ε))

theorem vectorBallReady_exists {b : ℕ → Fin 3 → QBall} {v : Space}
    (hb : ∀ j, QBall.Converges (fun n => b n j) (v j))
    {ε : ℚ} (hε : 0 < ε) : ∃ n, vectorBallReady b ε n := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have h : ∀ j, ∀ᶠ n in atTop, ((b n j).radius : ℝ) < ε := fun j =>
    (hb j).2.eventually_lt_const he
  obtain ⟨n, hn⟩ := (eventually_all.mpr h).exists
  exact ⟨n, fun j => by exact_mod_cast (hn j).le⟩

def evaluateVectorBalls (b : ℕ → Fin 3 → QBall) (ε : ℚ)
    (h : ∃ n, vectorBallReady b ε n) : RationalVector :=
  fun j => (b (Nat.find h) j).center

theorem evaluateVectorBalls_spec {v : Space} (b : ℕ → Fin 3 → QBall)
    (hb : ∀ j, QBall.Converges (fun n => b n j) (v j))
    (hc : ∀ n j, (b n j).Contains (v j)) (ε : ℚ) (hε : 0 < ε) :
    ‖v - rationalVector (evaluateVectorBalls b ε (vectorBallReady_exists hb hε))‖ ≤ (ε : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast hε.le)).mpr
  intro j
  change |v j - ((b (Nat.find (vectorBallReady_exists hb hε)) j).center : ℝ)| ≤ ε
  exact (hc _ j).trans (by exact_mod_cast (Nat.find_spec (vectorBallReady_exists hb hε) j))

end ForcedComputation

end OAI
