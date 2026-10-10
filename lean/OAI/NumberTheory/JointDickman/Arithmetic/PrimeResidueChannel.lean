import OAI.NumberTheory.JointDickman.Probability.IndependentKernelSplit
import OAI.NumberTheory.JointDickman.Probability.TwoSplitKernelComparison

namespace OAI

/-!
# The finite residue estimate for the actual fair-prime channel

This combines the actual two-split comparison, the independent low/high
decomposition, and the exclusive local law. The conclusion concerns the
original fair-split channel and every real input simultaneously.
-/

namespace JointDickman

open scoped BigOperators

noncomputable def fullPrimeMass (Q : Finset ℕ) : (Q → Bool) → ℝ :=
  bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ))

noncomputable def quarterPrimeMass (Q : Finset ℕ) : (Q → Bool) → ℝ :=
  bernoulliSiteMass (fun p : Q => 1 / (4 * (p.val : ℝ)))

noncomputable def fairPrimeTransition {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → A) : (Q → Bool) → A → ℝ :=
  fairSplitTransition (fun x => cell (retainedPrimeProduct Q x))

noncomputable def primeOutputCell {A : Type*} (Q : Finset ℕ) (cell : ℕ → A) :
    (Q → Bool) → (Q → Bool) → Option A :=
  primeProductCell Q (fun n => some (cell n))

theorem fullPrimeMass_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 ≤ fullPrimeMass Q x := by
  apply bernoulliSiteMass_nonneg
  intro p
  have hp := hQ p.val p.property
  have hp₀ : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
  exact ⟨by positivity, (div_le_one hp₀).mpr hp₁⟩

theorem quarterPrimeMass_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 ≤ quarterPrimeMass Q x := by
  apply bernoulliSiteMass_nonneg
  intro p
  have hp := hQ p.val p.property
  have hp₀ : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
  refine ⟨by positivity, (div_le_one (mul_pos (by norm_num) hp₀)).mpr ?_⟩
  linarith

theorem quarterPrimeMass_sum (Q : Finset ℕ) : ∑ x, quarterPrimeMass Q x = 1 :=
  bernoulliSiteMass_sum _

/-- The actual fair-split channel kernel and the independent triple kernel
are compared through their real cell-pair probabilities. -/
theorem fairPrimeKernel_independent_error {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → A) {m : ℝ} (hm : 0 < m) (a b : A) :
    |finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) a b -
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeOutputCell Q cell) a b / (m * m)| ≤ (9 / (8 * N : ℝ)) / (m * m) := by
  classical
  have hprob := twoSplitPrimeProducts_cell_tail_bound Q hQ hN hcut
    {n | cell n = a} {n | cell n = b}
  simp only [Set.mem_ofPred_eq] at hprob
  have hi : (∑ y, if cell (independentSplitProducts Q y).1 = a ∧
        cell (independentSplitProducts Q y).2 = b then
      bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0) =
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeOutputCell Q cell) a b := by
    simpa only [Option.some.injEq, quarterPrimeMass, primeOutputCell] using independentPrimeCellMass_eq_pair Q
      (fun p : Q => 1 / (4 * (p.val : ℝ))) (fun n => some (cell n)) a b
  change |finiteTwoSplitKernel
      (bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ))) (fun _ => m)
      (fairSplitTransition (fun x => cell (retainedPrimeProduct Q x))) a b - _| ≤ _
  rw [fairPrimeTransition_twoSplitKernel, ← hi, ← sub_div, abs_div,
    abs_of_pos (mul_pos hm hm)]
  apply div_le_div_of_nonneg_right _ (mul_pos hm hm).le
  convert hprob using 1
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ => x - y)
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all

/-- The nonnegative part discarded from the independent model. -/
noncomputable def primeLowUnionKernel {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → A) (low : (Q → Bool) → Prop) [DecidablePred low]
    (m : ℝ) : A → A → ℝ :=
  lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeOutputCell Q cell) low (fun _ => m)

noncomputable def primeHighExclusiveCell {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → A) (low : (Q → Bool) → Prop) [DecidablePred low] :
    (Q → Bool) → A → ℝ :=
  highExclusiveCell (quarterPrimeMass Q) (primeOutputCell Q cell) low

/-- The actual kernel minus the independent low union is uniformly flat,
with the explicit local-law and prime-comparison errors added together. -/
theorem fairPrimeKernel_discarded_flat_error {D R : Type*}
    [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → D × R)
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m η : ℝ} (hm : 0 < m) (hη : 0 ≤ η)
    (hlocal : ∀ c d r, |primeHighExclusiveCell Q cell low c (d, r) - profile c d| ≤ η)
    (d e : D) (r s : R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell)
          (d, r) (e, s) - primeLowUnionKernel Q cell low m (d, r) (e, s)) -
        flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e| ≤
      (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hind := independentPairKernel_cutoff (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeOutputCell Q cell) low (fun _ : D => m) (d, r) (e, s)
  have herr := fairPrimeKernel_independent_error Q hQ hN hcut cell hm (d, r) (e, s)
  have hhigh := exclusiveProductKernel_flat_error (quarterPrimeMass Q) (fun _ : D => m)
    (primeHighExclusiveCell Q cell low) profile hquarter (quarterPrimeMass_sum Q) (fun _ => hm)
    (fun c a => highExclusiveCell_nonneg _ _ _ hquarter c a)
    (fun c a => highExclusiveCell_le_one _ _ _ hquarter (quarterPrimeMass_sum Q) c a)
    hη hlocal d e r s
  change independentPairMass _ _ _ _ _ / (m * m) =
    primeLowUnionKernel Q cell low m (d, r) (e, s) +
      exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
        (primeHighExclusiveCell Q cell low) (d, r) (e, s) at hind
  rw [hind] at herr
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (fairPrimeTransition Q cell) (d, r) (e, s) - primeLowUnionKernel Q cell low m (d, r) (e, s)) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e =
    (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (fairPrimeTransition Q cell) (d, r) (e, s) -
        (primeLowUnionKernel Q cell low m (d, r) (e, s) +
          exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
            (primeHighExclusiveCell Q cell low) (d, r) (e, s))) +
    (exclusiveProductKernel (quarterPrimeMass Q) (fun _ : D => m)
      (primeHighExclusiveCell Q cell low) (d, r) (e, s) -
        flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- The complete finite residue-channel estimate. All analytic information
is isolated in the genuine marginal, common-cell and high-exclusive local
bounds; the kernel identities and operator estimate are proved here. -/
theorem fairPrimeResidueChannel_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → D × R)
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m H η : ℝ} (hm : 0 < m) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeOutputCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeOutputCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c d r, |primeHighExclusiveCell Q cell low c (d, r) - profile c d| ≤ η)
    (f : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) f a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) f (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * ((2 * η + η ^ 2 + 9 / (8 * N : ℝ)) / (m * m)) * ∑ _a : D × R, m) *
          ∑ x, fullPrimeMass Q x * f x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell)
  let L := primeLowUnionKernel Q cell low m
  have hL (a b : D × R) : 0 ≤ L a b :=
    lowUnionExclusiveKernel_nonneg _ _ _ _ _ hquarter hquarter (fun _ => hm.le) a b
  have hrows (a : D × R) : (∑ b : D × R, m * L a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H :=
    lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
      (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hflat := fairPrimeKernel_discarded_flat_error Q hQ hN hcut cell low profile hm hη hlocal
  have hε : 0 ≤ (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := residueChannel_square_of_discarded (fullPrimeMass Q) (fun _ : D => m)
    (fairPrimeTransition Q cell) L (fun a b => K a b - L a b)
    (flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile)
    (fullPrimeMass_nonneg Q hQ) (fun _ => hm) hL
    (fun a b => by dsimp [K]; ring)
    (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hrows hflat f
  convert hbound using 1
  ring

end JointDickman

end OAI
