import OAI.Probability.InvariantIsing.Cavity.CavityPrefixAffineFamily
import OAI.Probability.InvariantIsing.Cavity.OffsetBlockPrior
import OAI.Probability.InvariantIsing.Cavity.ConsecutiveRationalTrialWitness

namespace OAI

/-! The exact constrained increment on each affine dimension progression. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

def affineRestrictedIncrement {m n : ℕ} (hm : 2 ≤ m) (_hn : 0 < n)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) (lam : Fin m → ℝ)
    (u : (r : ℕ) → Fin (cavityPrefixAffineSize n (m*n-n+n+3) c r) → ℝ)
    (v : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  let N := cavityPrefixAffineSize n (m*n-n+n+3) c r
  let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
  let S := offsetBlockConstraint (r+(m*n-n+n+3)) R Cset
  let hS := offsetBlockConstraint_nonempty R hR Cset hCset
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  (∫ z, restrictedRotationLogMean (cavityProductSlice S Cset)
    (cavityProductSlice_nonempty S hS Cset hCset) z.2
    (diagonalPerturbedEigenvalues (fun i => lam (g (N+n) i))
      (cavitySpectralGroup (g (N+n))) (v r) 1)
    (cavitySpectralGroup (g (N+n))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N+n)).prod θ) -
  ∫ z, restrictedRotationLogMean S hS z.2
    (diagonalPerturbedEigenvalues (fun i => lam (g N i)) (cavitySpectralGroup (g N)) (v r) 1)
    (cavitySpectralGroup (g N)) (cavityBaseAmplitude (u r)) z.1 ∂(μ N).prod θ


end InvariantIsing

end

end OAI
