import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogPrimeObservable
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMixedMeasurable
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairHaarRegularity
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelTransport

namespace OAI

/-! # Measurability of the original two-prime pattern integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

theorem movingPatternLogPrimeObservable_measurable
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ) (x : Fin (N + 1) → primes) :
    Measurable (fun z : ℝ × ℝ =>
      movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist input Q z.2
        ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) logSlots cb x) := by
  have h := movingPatternPrimeObservable_measurable e t small slot perm pattern
    primes hprimes childBound pivotBound hfreq F E outside R r p g twist input Q
    ψ X lo hi hlo hhi φ G Bφ Dφ hBφ hDφ hφ hlip hout x
  exact measurable_const.mul h

end
end Ostmann

end OAI
