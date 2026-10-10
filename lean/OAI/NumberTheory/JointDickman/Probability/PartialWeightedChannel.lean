import OAI.NumberTheory.JointDickman.Probability.WeightedKernelCutoff
import OAI.NumberTheory.JointDickman.Arithmetic.PartialPrimeChannel
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCoarseChannel

namespace OAI

/-! # Coarse approximation for the partially retained weighted prime channel -/

namespace JointDickman

open scoped BigOperators NNReal

theorem independentPairKernel_weighted {C E D R : Type*} [Fintype C] [Fintype E]
    [DecidableEq D] [DecidableEq R]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option (D × R)) (weight : E → ℝ)
    (m : ℝ) (a b : D × R) :
    independentPairMass w v cell a b / (m * m) =
      weightedDiscardedKernel w v cell weight m a b +
        exclusiveProductKernel w (fun _ => m)
          (fun c => optionCellMass (fun e => v e * weight e) (cell c)) a b := by
  unfold weightedDiscardedKernel weightedDiscardedMass exclusiveProductKernel independentPairMass
  ring

theorem partialFairPrimeKernel_weighted_smooth_error {D R : Type*}
    [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (weight : (Q → Bool) → ℝ) (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m M η : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ c x, |f c x| ≤ M)
    (hlocal : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c) a / m -
        f c (location a)| ≤ η) (a b : D × R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
        weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) weight m a b) -
      smoothMixtureKernel (quarterPrimeMass Q) f location a b| ≤
        2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by
  have herr := partialFairPrimeKernel_independent_error Q hQ hN hcut cell hm a b
  rw [independentPairKernel_weighted _ _ _ weight] at herr
  have hhigh := exclusiveProductKernel_smooth_error (quarterPrimeMass Q)
    (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c))
    f location (quarterPrimeMass_nonneg Q hQ) (quarterPrimeMass_sum Q) hm.ne' hM hη hf hlocal a b
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) a b -
      weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) weight m a b) - smoothMixtureKernel (quarterPrimeMass Q) f location a b =
      (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
        (weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) weight m a b +
        exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
          (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c)) a b)) +
      (exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
          (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c)) a b -
        smoothMixtureKernel (quarterPrimeMass Q) f location a b) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- The discarded weighted mass is controlled by the low union. This
proves the coarse estimate for the actual partial-output channel. -/
theorem partialFairPrimeWeightedCoarse_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (weight : (Q → Bool) → ℝ) (low : (Q → Bool) → Prop) [DecidablePred low]
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1)
    (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m H M η mesh : ℝ} {L₀ : ℝ≥0}
    (hm : 0 < m) (hH : 0 ≤ H) (hM : 0 ≤ M) (hη : 0 ≤ η) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeProductCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c) a / m -
        f c (location a)| ≤ η)
    (g : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) g a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) g (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * (2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) +
          2 * M * (L₀ : ℝ) * mesh) * ∑ _a : D × R, m) *
            ∑ x, fullPrimeMass Q x * g x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
  let W := weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) weight m
  have hW (a b : D × R) : 0 ≤ W a b :=
    weightedDiscardedKernel_nonneg _ _ _ weight hquarter hquarter hweight hm.le a b
  have hrows (a : D × R) : (∑ b : D × R, m * W a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H := by
    calc
      _ ≤ ∑ b : D × R, m * lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) low (fun _ => m) a b := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left
          (weightedDiscardedKernel_le_lowUnion _ _ _ weight low hquarter hquarter
            hweight hhigh hm.le a b) hm.le
      _ ≤ _ := lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
        (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hsmooth := partialFairPrimeKernel_weighted_smooth_error Q hQ hN hcut cell weight f location
    hm hM hη hf hlocal
  have hε : 0 ≤ 2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := coarseChannel_square_bound (fullPrimeMass Q) (partialFairPrimeTransition Q cell)
    (quarterPrimeMass Q) f location W (fun a b => K a b - W a b)
    (fullPrimeMass_nonneg Q hQ) hquarter (quarterPrimeMass_sum Q)
    hm (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hM hmesh hf hLip hdiam hW hrows
    (fun a b => by dsimp [K]; ring) hsmooth g
  convert hbound using 1
  ring

end JointDickman

end OAI
