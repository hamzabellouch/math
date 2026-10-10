import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Extend a finite phase by keeping its final increment constant. -/
def affineTailPhase (f : ℕ → ℝ) (N n : ℕ) : ℝ :=
  f 0 + ∑ j ∈ Finset.range n,
    (f (min j (N - 1) + 1) - f (min j (N - 1)))

theorem affineTailPhase_increment (f : ℕ → ℝ) (N n : ℕ) :
    affineTailPhase f N (n + 1) - affineTailPhase f N n =
      f (min n (N - 1) + 1) - f (min n (N - 1)) := by
  simp only [affineTailPhase, Finset.sum_range_succ]
  ring

theorem affineTailPhase_eq (f : ℕ → ℝ) (N : ℕ) :
    ∀ n : ℕ, n ≤ N → affineTailPhase f N n = f n := by
  intro n
  induction n with
  | zero => simp [affineTailPhase]
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hmin : min n (N - 1) = n := Nat.min_eq_left (by omega)
    have hinc := affineTailPhase_increment f N n
    rw [hmin] at hinc
    linarith

theorem affineTailPhase_increment_monotone (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    Monotone (fun j => affineTailPhase f N (j + 1) - affineTailPhase f N j) := by
  intro i j hij
  dsimp only
  rw [affineTailPhase_increment, affineTailPhase_increment]
  apply hmono
  · change min i (N - 1) < N
    omega
  · change min j (N - 1) < N
    omega
  · omega

theorem affineTailPhase_increment_antitone (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : AntitoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    Antitone (fun j => affineTailPhase f N (j + 1) - affineTailPhase f N j) := by
  intro i j hij
  dsimp only
  rw [affineTailPhase_increment, affineTailPhase_increment]
  apply hmono
  · change min i (N - 1) < N
    omega
  · change min j (N - 1) < N
    omega
  · omega

theorem affineTailPhase_increment_eq (f : ℕ → ℝ) (N j : ℕ) (hj : j < N) :
    affineTailPhase f N (j + 1) - affineTailPhase f N j = f (j + 1) - f j := by
  rw [affineTailPhase_increment, Nat.min_eq_left (by omega : j ≤ N - 1)]

/-- Local interval monotonicity is enough whenever a phase-sum theorem assumes
globally monotone increments: this extension preserves every sample used. -/
theorem exists_monotone_increment_extension (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    ∃ g : ℕ → ℝ, (∀ j, j ≤ N → g j = f j) ∧
      Monotone (fun j => g (j + 1) - g j) ∧
      (∀ j, j < N → g (j + 1) - g j = f (j + 1) - f j) := by
  exact ⟨affineTailPhase f N, affineTailPhase_eq f N,
    affineTailPhase_increment_monotone f N hN hmono,
    affineTailPhase_increment_eq f N⟩

/-- The corresponding decreasing-increment extension. -/
theorem exists_antitone_increment_extension (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : AntitoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    ∃ g : ℕ → ℝ, (∀ j, j ≤ N → g j = f j) ∧
      Antitone (fun j => g (j + 1) - g j) ∧
      (∀ j, j < N → g (j + 1) - g j = f (j + 1) - f j) := by
  exact ⟨affineTailPhase f N, affineTailPhase_eq f N,
    affineTailPhase_increment_antitone f N hN hmono,
    affineTailPhase_increment_eq f N⟩

end Problem337

end

end OAI
