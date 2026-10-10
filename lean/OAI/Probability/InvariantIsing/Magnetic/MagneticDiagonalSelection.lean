import OAI.Probability.InvariantIsing.Magnetic.MagneticDiagonalL1Consistency
import OAI.Probability.InvariantIsing.Arrays.OverlapTestDiagonal

namespace OAI

/-! Selection of one increasing finite-depth diagonal and one compact
quantile subsequence for growing attainable constrained blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem exists_magnetic_consistent_diagonal {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (mag : ℕ → A → ℝ)
    {s : ℝ} (hs : s < 1) (hmag : ∀ r a, |mag r a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag r a)/2))
    (base : ℕ → OverlapPath)
    (htest : ∀ r (Φ : ℝ →ᵇ ℝ), Tendsto (fun j =>
      ∫ t, Φ (cavityStrictUniformPath (base r) j t) *
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField rho lam hrho hsum (base r) j) t -
          cavityStrictUniformPath (base r) j t) ∂pathMeasure) atTop (𝓝 0)) :
    ∃ (d φ : ℕ → ℕ) (p : OverlapPath), StrictMono d ∧ StrictMono φ ∧
      Tendsto (fun r => ∫ t, |cavityStrictUniformPath (base (φ r)) (d (φ r)) t-p t|
        ∂pathMeasure) atTop (𝓝 0) ∧
      Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN (φ r))
        (spinGroupSlice (group (φ r)) (k (φ r)))
        (spinGroupSlice_nonempty (group (φ r)) (k (φ r)) (hk (φ r)))
        (cavityStrictUniformField rho lam hrho hsum (base (φ r)) (d (φ r))) t-p t|
        ∂pathMeasure) atTop (𝓝 0) := by
  let q := fun r j => cavityStrictUniformPath (base r) j
  let B := fun r j => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r))
    (cavityStrictUniformField rho lam hrho hsum (base r) j)
  obtain ⟨d, hd, hdiag⟩ := exists_diagonal_overlap_tests q B htest
  obtain ⟨p, φ, hφ, hpoint, hL1⟩ := overlapPath_ae_l1_subsequence (fun r => q r (d r))
  refine ⟨d, φ, p, hd, hφ, hL1, ?_⟩
  apply magnetic_diagonal_l1_of_constrained_tests rho lam hrho hsum hK hlam
    (fun r => N (φ r)) (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop)
    (fun r => group (φ r)) (fun r => k (φ r)) (fun r => hk (φ r))
    (fun r => mag (φ r)) hs (fun r => hmag (φ r)) (fun r => hc (φ r))
    (fun r => base (φ r)) (fun r => d (φ r)) p hpoint
  intro Φ
  exact (hdiag Φ).comp hφ.tendsto_atTop

end InvariantIsing

end

end OAI
