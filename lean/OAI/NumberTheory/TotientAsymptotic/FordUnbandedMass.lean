import OAI.NumberTheory.TotientAsymptotic.UnbandedSimplexMass
import OAI.NumberTheory.TotientAsymptotic.SimplexCube

namespace OAI

/-! Prime-prefix mass with Ford's literal row parameters. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma xi_eq_simplexBoxError (x : ℝ) (i : ℕ) :
    xi x i = 1+simplexBoxError 0 (m x-i) := by
  have he : (Real.exp (-(1/40:ℝ)))^(m x-i) =
      Real.exp (-((m x-i:ℕ):ℝ)/40) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold xi simplexBoxError
  rw [he]
  ring

theorem ford_unbanded_prime_mass : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, H < m x →
    ∀ Q : Finset (Fin (m x-H) → ℕ),
      (∀ p ∈ Q, (∀ i, (p i).Prime) ∧
        primePrefixCoord p ∈ enlargedSimplex (m x-H) (B x)
          (xi x 0) (fun i => xi x (i.val+1)) ∧
        (∀ i, i.val+1=m x-H → (1/100:ℝ) ≤ primePrefixCoord p i)) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤ C*G x (m x-H) := by
  obtain ⟨C,hC,hbound⟩ := unbanded_simplex_prime_mass
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with x hx
  intro H hH Q hQ
  apply hx H hH Q
  intro p hp
  simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using hQ p hp

end TotientAsymptotic

end

end OAI
