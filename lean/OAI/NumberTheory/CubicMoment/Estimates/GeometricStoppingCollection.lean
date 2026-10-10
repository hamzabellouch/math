import OAI.NumberTheory.CubicMoment.Estimates.GeometricStoppingKernel

namespace OAI

/-! Exact independent-factor reconstruction of all stopped squarefree
terms. The original finite support remains a product test. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The full stopping-label sum reconstructs the original finite sum.
The kernel and support are unchanged, including any sharp product cutoff. -/
theorem geometric_stopping_collection (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) {Z : ℝ} (hstart : norm r < Z)
    (hend : ∀ n ∈ S, Z ≤ norm r*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X))
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
    ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
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
  have hF (n : Eisenstein) (hn : n ∈ S) :
      (∑ q ∈ stoppingLabelBox ρ X,
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*F q n) = cutoffMoebius ψ w n*K n := by
    obtain ⟨hnp,hns,hnX⟩ := hS n hn
    have h := geometric_label_stopping_kernel hnp hns hρ hρ₂ hX hnX
      (norm_pos_of_ne_zero (primary_ne_zero hr)) hstart (hend n hn) ψ w K
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro q _hq
    dsimp only [F,bin,ell]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    split_ifs <;> ring
  calc
    _ = ∑ n ∈ S, ∑ q ∈ stoppingLabelBox ρ X,
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*F q n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hF n hn).symm
    _ = ∑ q ∈ stoppingLabelBox ρ X,
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*∑ n ∈ S, F q n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _hq
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
