import OAI.NumberTheory.Ostmann.Arithmetic.MovingCutoffPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierSupported

namespace OAI

/-! # Keeping the original logarithmic cutoff in every moving node -/

namespace Ostmann
open scoped Classical

noncomputable def movingNaturalNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) : {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingNaturalNodeCutoff value φ G left p L * movingNaturalNodeCutoff value φ G right p R

theorem movingNaturalNodeCutoff_star {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n) (L R : ℕ) :
    star (movingNaturalNodeCutoff value φ G T L R) = movingNaturalNodeCutoff value φ G T L R := by
  have hstar (a : ℝ) : star (a : ℂ) = (a : ℂ) := by simp
  induction T generalizing L R with
  | leaf => simp only [movingNaturalNodeCutoff, star_one]
  | node s CL CR u left right ihL ihR =>
    simp only [movingNaturalNodeCutoff, star_mul, hstar, ihL, ihR]
    ring

noncomputable def movingPhiExtra {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  extra x s v w * positiveLogCutoff φ (G x.depth)
    ((historyPivot (movingSlotSystem value childBound pivotBound) x s v w / x.compensation value : ℕ) : ℝ)

/-- The smooth cutoff is factored out of the original recursion, even when
an arithmetic guard vanishes. All other node factors remain in `extra`. -/
theorem movingSlotWeight_node_cutoff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t) (L R : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingPhiExtra value childBound pivotBound extra φ G))
        n ⟨n, T, L, R⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, L, R⟩ t *
          movingNaturalNodeCutoff value φ G T L R := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound extra
  let cutφ := movingSlotCutoff value childBound pivotBound (movingPhiExtra value childBound pivotBound extra φ G)
  induction T generalizing L R with
  | leaf s regular => simp only [recursiveTransferWeight, movingNaturalNodeCutoff, mul_one]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, L, R⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value L R
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hc : (cutφ x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) =
        (cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
          (positiveLogCutoff φ (G (n + 1)) p : ℂ) := by
      dsimp only [cutφ, cut, movingSlotCutoff, movingPhiExtra]
      split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero, zero_mul]
      congr 2
      change positiveLogCutoff φ (G (n + 1)) ((historyPivot sys x t.1 _ _ / MovingSlotReversal.naturalProduct value u : ℕ) : ℝ) = _
      rw [hp]
    change recursiveTransferWeight sys F cutφ (n + 1) x t = _
    simp only [recursiveTransferWeight]
    split_ifs
    · change (cutφ x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys F cutφ n ⟨n, left, _, L⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutφ n ⟨n, right, _, R⟩ t.2.2) =
        ((cut x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cut n ⟨n, left, _, L⟩ t.2.1 *
          star (recursiveTransferWeight sys F cut n ⟨n, right, _, R⟩ t.2.2)) * _
      rw [hp, hc, ihL t.2.1 hT.2.1 p L, ihR t.2.2 hT.2.2 p R]
      simp only [star_mul, movingNaturalNodeCutoff_star]
      change _ = _ * ((positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingNaturalNodeCutoff value φ G left p L * movingNaturalNodeCutoff value φ G right p R)
      ring
    · exact (zero_mul _).symm

theorem movingNaturalNodeCutoff_eq_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : ℕ) (hI : T.Integral value L R) :
    movingNaturalNodeCutoff value φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).realPivot_eq value L R hf.1
      (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    simp only [movingNaturalNodeCutoff, movingRealNodeCutoff, hp,
      ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

end Ostmann

end OAI
