import OAI.NumberTheory.CubicMoment.Decomposition.StoppingTwoStage
import OAI.NumberTheory.CubicMoment.Estimates.GeometricStoppingCollection

namespace OAI

/-! Exact primary-pair collection on an arbitrary finite stopping-label
set. No end-crossing premise is needed for this fixed-label identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometric_stopping_label_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ρ Z : ℝ) (r : Eisenstein) (I : Finset (ℕ × ℕ × ℕ))
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, ∑ q ∈ I, geometricStoppingLabel ρ X (norm r) Z ψ w K n q) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 Z r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  let bin := geometricPrimeBin ρ X
  let ell := geometricBinLower ρ X
  let F := fun (q : ℕ × ℕ × ℕ) (n : Eisenstein) =>
    ∑ t ∈ (primeBin (primaryPrimeFactors n) bin q.1).powersetCard q.2.1,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin q.1 t) bin q.1).card = q.2.2 ∧
          (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin q.1 t) bin ell/
              ell q.1 < Z ∧
            Z ≤ norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin q.1 t) bin ell) then
        cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin q.1 t, p)*
          cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin q.1 t, p)*
          K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin q.1 t, p)*
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin q.1 t, p))
      else 0
  have hF (q : ℕ × ℕ × ℕ) (n : Eisenstein) :
      geometricStoppingLabel ρ X (norm r) Z ψ w K n q =
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ * F q n := by
    dsimp only [geometricStoppingLabel,F,bin,ell]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    split_ifs <;> ring
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  simp_rw [hF]
  rw [←Finset.mul_sum]
  congr 1
  let G := fun d e : Eisenstein =>
    if stoppingSideTest bin ell q.1 q.2.1 Z r d ∧
        stoppingRemainingTest bin q.1 q.2.2 e then
      cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0
  calc
    _ = ∑ n ∈ S,
        ∑ p ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
            (fun p => p.1*p.2 = n), G p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnp,hns,hnX⟩ := hS n hn
      exact stopping_primary_pair_sum hnp hns hnX bin ell q.1 q.2.1 q.2.2 Z r ψ w
        (fun d e => K (d*e))
    _ = _ := primary_pair_fiber_support S X G

end CubicFirstMoment

end

end OAI
