import OAI.NumberTheory.Jacobsthal.Primes.GuardedHardPrimeSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
  ErdosVarianceLargePrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_guarded_hard_count (alpha aStar eps sigma Cmin : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        ∀ r : ℚ,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) ≤
          sigma*((primeBin R theta).card : ℝ) := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_hard_bad_prime_fraction alpha aStar eps sigma Cmin halpha ha heps hsigma
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hsource xi hxi hxib] with z hz
  intro R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry r
  by_cases hg : hardCandidate z R a r qf Cs
  · have hb := hz R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hg.1 hg.2.1 hg.2.2
    rw [guardedHardPrimes,ite_eq_left hg]
    exact subset_card_of_fraction _ _ (Finset.filter_subset _ _) sigma hb
  · simp only [guardedHardPrimes,ite_eq_right hg,Finset.card_empty,Nat.cast_zero]
    positivity

end ErdosVarianceWeighted

end

end Erdos970

end OAI
