import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport

namespace OAI

/-! # The full smooth giant law inside an ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantMass_ambient (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) :
    smoothGiantMass P φ G = smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  symm
  apply Finset.sum_subset hsub
  intro p hp hn
  have hz : φ (Real.log p - G) = 0 := by
    by_contra hne
    exact hn (smoothGiant_prime_support φ G hout p (hP p hp) hne)
  simp only [hz, zero_div]

theorem smoothGiantPrior_ambient_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
    smoothGiantPrior P φ G p = 0 := by
  have hz : φ (Real.log (p : ℕ) - G) = 0 := by
    by_contra hne
    exact hp (smoothGiant_prime_support φ G hout p (hP p p.property) hne)
  simp only [smoothGiantPrior, hz, mul_zero, zero_div]

theorem smoothGiantPrior_ambient_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) (f : P → ℝ) :
    (∑ p : P, smoothGiantPrior P φ G p * f p) =
      ∑ q : smoothGiantPrimeRange G, smoothGiantPrior (smoothGiantPrimeRange G) φ G q *
        f ⟨q, hsub q.property⟩ := by
  have hm := smoothGiantMass_ambient P hP φ G hout hsub
  let e : smoothGiantPrimeRange G → P := fun q => ⟨q, hsub q.property⟩
  have hprior (q : smoothGiantPrimeRange G) : smoothGiantPrior P φ G (e q) =
      smoothGiantPrior (smoothGiantPrimeRange G) φ G q := by
    simp only [smoothGiantPrior, smoothGiantLogNormalizer, hm, e]
  have hz (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
      smoothGiantPrior P φ G p * f p = 0 := by
    rw [smoothGiantPrior_ambient_zero P hP φ G hout p hp, zero_mul]
  calc
    _ = ∑ p ∈ (Finset.univ : Finset P).filter (fun p : P => (p : ℕ) ∈ smoothGiantPrimeRange G),
        smoothGiantPrior P φ G p * f p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (p : ℕ) ∈ smoothGiantPrimeRange G
      · simp only [hp, ite_true]
      · simp only [hp, ite_false, hz p hp]
    _ = ∑ q : smoothGiantPrimeRange G, smoothGiantPrior P φ G (e q) * f (e q) := by
      symm
      apply Finset.sum_bij (fun q _ => e q)
      · intro q _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.property⟩
      · intro q _ r _ hqr
        exact Subtype.ext (congrArg (fun p : P => p.val) hqr)
      · intro p hp
        refine ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, ?_⟩
        rfl
      · intro q _
        rfl
    _ = _ := by simp only [hprior, e]

end Ostmann

end OAI
