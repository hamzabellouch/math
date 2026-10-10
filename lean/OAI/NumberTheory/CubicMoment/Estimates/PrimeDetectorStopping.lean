import OAI.NumberTheory.CubicMoment.Decomposition.StoppingThreshold

namespace OAI

/-! The actual primary-divisor rough weight split into un-stopped and
stopped pieces. Every divisor support fact follows from divisibility. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_divisor_stopping_support {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {X : ℝ} (hnX : norm n ≤ X) :
    ∀ d ∈ metaplecticPrimaryDivisors n, primary d ∧ Squarefree d ∧ norm d ≤ X := by
  intro d hd
  obtain ⟨hdball,hdn⟩ := Finset.mem_filter.mp hd
  have hdprim := (mem_primaryElementBall.mp hdball).1
  exact ⟨hdprim,fun p hp => hs p (hp.trans hdn),
    (norm_le_of_dvd (primary_ne_zero hn) hdn).trans hnX⟩

/-- The inner rough-product factor is split at the actual surrogate
threshold. The original kernel is kept constant through the divisor
expansion, so its sharp norm cutoff is unchanged. -/
theorem roughProduct_primary_stopping_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnX : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (roughProduct ψ w n:ℂ)*K n =
      (∑ d ∈ metaplecticPrimaryDivisors n with R*primeSurrogate (primaryPrimeFactors d)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w d*K n) +
      ∑ d ∈ metaplecticPrimaryDivisors n,
        geometricStoppedElement ρ X R Z ψ w (fun _ => K n) d := by
  rw [roughProduct_primary_divisor_sum hn hs,Finset.sum_mul]
  exact finite_stopping_threshold_split (metaplecticPrimaryDivisors n) hρ hρ₂ hX
    (primary_divisor_stopping_support hn hs hnX) hR hstart ψ w (fun _ => K n)

/-- The same exact split after summing any finite original support. -/
theorem roughProduct_finite_stopping_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, (roughProduct ψ w n:ℂ)*K n) =
      (∑ n ∈ S, ∑ d ∈ metaplecticPrimaryDivisors n with
          R*primeSurrogate (primaryPrimeFactors d)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w d*K n) +
      ∑ n ∈ S, ∑ d ∈ metaplecticPrimaryDivisors n,
        geometricStoppedElement ρ X R Z ψ w (fun _ => K n) d := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact roughProduct_primary_stopping_split (hS n hn).1 (hS n hn).2.1 hρ hρ₂ hX
    (hS n hn).2.2 hR hstart ψ w K

end CubicFirstMoment

end

end OAI
