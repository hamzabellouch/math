import OAI.NumberTheory.JointDickman.Arithmetic.PrimeResidueChannel

namespace OAI

/-! # Fair-prime channels restricted to a collection of output cells -/

namespace JointDickman

open scoped BigOperators

noncomputable def partialFairPrimeTransition {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) (a : A) : ℝ :=
  optionCellMass (fairRetentionMass x) (fun y => cell (retainedPrimeProduct Q y)) a

theorem partialFairPrimeTransition_nonneg {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) (a : A) :
    0 ≤ partialFairPrimeTransition Q cell x a :=
  optionCellMass_nonneg _ _ (fairRetentionMass_nonneg x) a

theorem partialFairPrimeTransition_sum_le {A : Type*} [Fintype A] [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) :
    (∑ a, partialFairPrimeTransition Q cell x a) ≤ 1 := by
  have h := optionCellMass_sum_le (fairRetentionMass x) (fun y => cell (retainedPrimeProduct Q y))
    (fairRetentionMass_nonneg x)
  simpa only [partialFairPrimeTransition, fairRetentionMass_sum] using h

theorem partialFairPrimeTransition_marginal {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (a : A) :
    (∑ x, fullPrimeMass Q x * partialFairPrimeTransition Q cell x a) =
      optionCellMass (bernoulliSiteMass (fun p : Q => (1 / (p.val : ℝ)) / 2))
        (fun y => cell (retainedPrimeProduct Q y)) a := by
  classical
  unfold partialFairPrimeTransition optionCellMass fullPrimeMass
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : cell (retainedPrimeProduct Q y) = some a
  · simp only [hy, ite_true]
    exact fairRetentionMass_marginal _ y
  · simp [hy]

/-- The same actual two-split comparison applies when outputs outside
all cells are discarded. -/
theorem partialFairPrimeKernel_independent_error {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option A) {m : ℝ} (hm : 0 < m) (a b : A) :
    |finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) a b / (m * m)| ≤ (9 / (8 * N : ℝ)) / (m * m) := by
  have h := fairPrimeKernel_independent_error Q hQ hN hcut cell hm (some a) (some b)
  convert h using 1
  simp only [finiteTwoSplitKernel, partialFairPrimeTransition, fairPrimeTransition,
      fairSplitTransition, independentPairMass, primeOutputCell, primeProductCell,
      optionCellMass, Option.some.injEq]
  congr 6

/-- A local profile independent of the residue yields a flat retained
kernel for the partial output channel. -/
theorem partialFairPrimeKernel_flat_error {D R : Type*} [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m η : ℝ} (hm : 0 < m) (hη : 0 ≤ η)
    (hlocal : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low c (d, r) -
        profile c d| ≤ η) (d e : D) (r s : R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
        (d, r) (e, s) -
      lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s)) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e| ≤
      (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by
  have hw := quarterPrimeMass_nonneg Q hQ
  have hind := independentPairKernel_cutoff (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) low (fun _ : D => m) (d, r) (e, s)
  have herr := partialFairPrimeKernel_independent_error Q hQ hN hcut cell hm (d, r) (e, s)
  have hhigh := exclusiveProductKernel_flat_error (quarterPrimeMass Q) (fun _ => m)
    (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) profile hw
    (quarterPrimeMass_sum Q) (fun _ => hm)
    (fun c a => highExclusiveCell_nonneg _ _ _ hw c a)
    (fun c a => highExclusiveCell_le_one _ _ _ hw (quarterPrimeMass_sum Q) c a)
    hη hlocal d e r s
  rw [hind] at herr
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) (d, r) (e, s) -
      lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s)) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e =
    (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) (d, r) (e, s) -
      (lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s) +
      exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
        (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) (d, r) (e, s))) +
      (exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
        (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) (d, r) (e, s) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- Residue centering for the actual channel with discarded outputs. -/
theorem partialFairPrimeResidueChannel_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m H η : ℝ} (hm : 0 < m) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeProductCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low c (d, r) -
        profile c d| ≤ η)
    (f : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) f a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
            f (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * ((2 * η + η ^ 2 + 9 / (8 * N : ℝ)) / (m * m)) * ∑ _a : D × R, m) *
          ∑ x, fullPrimeMass Q x * f x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
  let L := lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) low (fun _ => m)
  have hL (a b : D × R) : 0 ≤ L a b :=
    lowUnionExclusiveKernel_nonneg _ _ _ _ _ hquarter hquarter (fun _ => hm.le) a b
  have hrows (a : D × R) : (∑ b : D × R, m * L a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H :=
    lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
      (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hflat := partialFairPrimeKernel_flat_error Q hQ hN hcut cell low profile hm hη hlocal
  have hε : 0 ≤ (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := residueChannel_square_of_discarded (fullPrimeMass Q) (fun _ : D => m)
    (partialFairPrimeTransition Q cell) L (fun a b => K a b - L a b)
    (flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile)
    (fullPrimeMass_nonneg Q hQ) (fun _ => hm) hL
    (fun a b => by dsimp [K]; ring)
    (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hrows hflat f
  convert hbound using 1
  ring

end JointDickman

end OAI
