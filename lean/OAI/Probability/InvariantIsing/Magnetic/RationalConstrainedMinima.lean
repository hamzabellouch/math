import OAI.Probability.InvariantIsing.Magnetic.MagneticRationalIncrementLower

namespace OAI

/-! Actual compact minimizers of each physical rational product-constraint objective. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology BigOperators
namespace InvariantIsing

theorem rational_constrained_minimizers_exist
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (spec : Fin m → ℕ) (hspec : ∑ a, spec a=n)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant] (lam : Fin m → ℝ) :
    ∃ (u : (j : ℕ) → Fin (cavityRationalSize n (m*n-n) j) → ℝ) (v : ℕ → Fin m → ℝ),
      (∀ j i, u j i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ j a, v j a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        rationalConstrainedObjective hm hn spec hspec Cset hCset μ lam j (u j) (v j) ≤
          rationalConstrainedObjective hm hn spec hspec Cset hCset μ lam j u' v' := by
  let N := fun j => (j+(m*n-n+n+3))*n
  let g := fun M => cavityRationalLabel (by omega : 0 < m) spec hspec M
  let S : (j : ℕ) → Finset (Spin (N j)) := fun j => consecutiveBlockConstraint n (j+(m*n-n+n+3)) Cset
  have hN j : 3 ≤ N j := cavityRationalSize_ge_three n (m*n-n) j hn
  have hpos j : 0 < N j := by have := hN j; omega
  let ν := fun j => cavityOrientedBaseLaw (hpos j) (μ (N j))
  have hν j : (ν j).IsMulLeftInvariant := cavityOrientedBaseLaw_leftInvariant (hpos j) (μ (N j))
  let π : (j : ℕ) → Measure (Spin (N j) × LabeledLeaf 0) := fun j =>
    restrictedZeroTreePrior (S j) (consecutiveBlockConstraint_nonempty Cset hCset)
  let (j : ℕ) : IsProbabilityMeasure (π j) :=
    restrictedZeroTreePrior_probability (S j) (consecutiveBlockConstraint_nonempty Cset hCset)
  choose u v hu hv hmin using fun j => priorPerturbationObjective_exists_minimum hhaar hgauss (hN j)
    (ν j) (hν j) (π j) (fun i => lam (g (N j) i)) (fun _ => 0) (cavitySpectralGroup (g (N j))) 1
    (fun _ => 0) monotone_const le_rfl
  exact ⟨u,v,hu,hv,hmin⟩

end InvariantIsing

end

end OAI
