import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalTrajectory

namespace OAI

/-! # Physical initial data as a continuous linear equivalence

For a fixed starting scale this map restores the physical amplitude and
changes the exact expanding Fourier norm to the standard Sobolev norm.
-/

open Set

namespace DefocusingNLS

noncomputable def expandingPhysicalInitialEquiv (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    FourierL2 ≃L[ℂ] FourierL2 :=
  (Units.mk0 (((L ^ (2 * a) : ℝ) : ℂ))
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by linarith : 0 < L) _).ne')) •
      ((ContinuousLinearEquiv.ofUnit (expandingWeightUnit a k L ha hk hL)).symm.trans
        (expandingSobolevEquiv a k ha ha1 hk))

theorem expandingPhysicalInitialEquiv_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    expandingPhysicalInitialEquiv a k L ha ha1 hk hL f =
      ((L ^ (2 * a) : ℝ) : ℂ) •
        expandingToSobolev a k ha1 hk (expandingInverseTransfer a k L ha hk hL f) := rfl

theorem expandingSchrodingerTrajectory_initial_equiv (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, FourierL2)) :
    expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u 0 =
      expandingPhysicalInitialEquiv a k L ha ha1 hk hL (u ⟨0, le_rfl, hS⟩) := by
  rw [expandingSchrodingerTrajectory_zero, expandingPhysicalInitialEquiv_apply]

/-- Open sets in the exact starting norm give open sets of physical `H^k` data. -/
theorem expandingPhysicalInitialEquiv_isOpen_image (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (V : Set FourierL2) (hV : IsOpen V) :
    IsOpen (expandingPhysicalInitialEquiv a k L ha ha1 hk hL '' V) :=
  (expandingPhysicalInitialEquiv a k L ha ha1 hk hL).toHomeomorph.isOpenMap V hV

theorem expandingPhysicalInitialEquiv_nonempty_image (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (V : Set FourierL2) (hV : V.Nonempty) :
    (expandingPhysicalInitialEquiv a k L ha ha1 hk hL '' V).Nonempty :=
  hV.image _

end DefocusingNLS

end OAI
