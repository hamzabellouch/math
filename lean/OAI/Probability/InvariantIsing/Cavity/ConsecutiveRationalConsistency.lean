import OAI.Probability.InvariantIsing.Cavity.ConsecutiveRationalMinimumConsistency

namespace OAI

/-! Weak constrained block self-consistency from actual physical minimizers, with no auxiliary model premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem consecutive_rational_weak_self_consistency
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (lam : Fin m → ℝ) (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax) :
    ∃ p : OverlapPath, ∀ Φ : ℝ →ᵇ ℝ,
      Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
        (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField
          (fun a => (s a : ℝ)/n) lam (cavityRationalMass_positive s hs hn)
          (cavityRationalMass_sum s hsum hn) p r) t-cavityStrictUniformPath p r t) ∂pathMeasure)
        atTop (𝓝 0) := by
  let N := fun r => (r+(m*n-n+n+3))*n
  let g := fun M => cavityRationalLabel (by omega : 0 < m) s hsum M
  let S : (r : ℕ) → Finset (Spin (N r)) :=
    fun r => consecutiveBlockConstraint n (r+(m*n-n+n+3)) Cset
  have hN r : 3 ≤ N r := cavityRationalSize_ge_three n (m*n-n) r hn
  have hpos r : 0 < N r := by have := hN r; omega
  let ν := fun r => cavityOrientedBaseLaw (hpos r) (μ (N r))
  have hν r : (ν r).IsMulLeftInvariant := cavityOrientedBaseLaw_leftInvariant (hpos r) (μ (N r))
  let π : (r : ℕ) → Measure (Spin (N r) × LabeledLeaf 0) := fun r =>
    restrictedZeroTreePrior (S r) (consecutiveBlockConstraint_nonempty Cset hCset)
  let (r : ℕ) : IsProbabilityMeasure (π r) :=
    restrictedZeroTreePrior_probability (S r) (consecutiveBlockConstraint_nonempty Cset hCset)
  choose u v hu hv hmin using fun r => priorPerturbationObjective_exists_minimum hhaar hgauss (hN r)
    (ν r) (hν r) (π r)
    (fun i => lam (g (N r) i)) (fun _ => 0) (cavitySpectralGroup (g (N r))) 1
    (fun _ => 0) monotone_const le_rfl
  exact consecutive_rational_minimizers_weak_consistency hhaar hgauss hpub hm hn s hs hsum
    Cset hCset μ lam amax hmax u v hu hv hmin

end InvariantIsing

end

end OAI
