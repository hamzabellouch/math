import OAI.MeasureTheory.Falconer.Estimates.ScalarSelectedForks
import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryGeometric

namespace OAI

/-! Applying the fixed-fold sumset construction to actual selected
 dyadic forks, with explicit scale margins. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_selected_fork_sumset {N copies J L : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty)
    (t : ℕ) (a b branch n : ℕ → ℕ)
    (hab : ∀ i < t, a i ≤ b i) (hnext : ∀ i < t, b i ≤ a (i+1))
    (hb : ∀ i < t, b i ≤ N)
    (hlevel : ∀ i < t, ScalarBranchingLevel Q (a i) (b i) (branch i) (n i))
    (hbranch : ∀ i < t, branch i ≠ 0)
    (scale : ℕ → ℝ) (hs : ∀ i ≤ t, 0 < scale i) (hJ : 0 < J)
    (hcontract : ∀ i < t, scale (i+1)*(1+2*(J:ℝ)*U) ≤ scale i)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies)
    (hlow : ∀ i < t, 2*scale (i+1) ≤ 6*(1/2:ℝ)^(n i))
    (hhigh : ∀ i < t, 18*(1/2:ℝ)^(n i) ≤ U*scale (i+1)) :
    ∃ E : Finset ℝ, E ⊆ copies • Q.image scalarPathCenter ∧ E.card = (J+1)^t ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → scale t ≤ |x-y| := by
  obtain ⟨f,hf,hbits⟩ := scalar_selected_binary_forks Q hQ hne t a b branch n hab hnext hb hlevel hbranch
  apply scalar_scaled_binary_growth f (Q.image scalarPathCenter) hf scale hs hJ hcontract hL hcopies
  · intro i w hw
    exact (hlow i i.isLt).trans (hbits i w hw).1
  · intro i w hw
    exact (hbits i w hw).2.trans (hhigh i i.isLt)

end Falconer.Regularization

end OAI
