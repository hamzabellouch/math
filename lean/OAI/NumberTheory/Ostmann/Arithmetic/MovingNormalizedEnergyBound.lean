import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedStatistic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeStatisticBound

namespace OAI

/-! # The arithmetic energy bounds the original normalized giant average -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The four unit-rectangle energy bounds give the full original giant law.
The factors from the two harmonic normalizations are retained explicitly. -/
theorem movingPrimeCore_normalized_energy_bound {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφnorm : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hν : ∀ b a, 0 ≤ ν b a) (hmass : ∀ b, ∑ a, ν b a = 1)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (gLeft gRight E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ i j : Bool,
      let u := if i then gLeft else gLeft - 1
      let r := if j then gRight else gRight - 1
      (movingOriginalSymmetrizedEnergy q value outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n m small slot greg gLeft gRight false u (u + 1) r (r + 1) u).re ≤ E) :
    ‖smoothGiantExternalAverage ν (V n) φ gLeft gRight (fun s y p r =>
      movingPrimeCore q value outside μ childBound pivotBound V f g Dq S ψ X lo hi φ G
        n m small slot greg ggiant favorable s y (Real.log p) (Real.log r))‖ ^ 2 ≤
      16 * Real.exp (2 * (smoothGiantLogNormalizer (smoothGiantPrimeRange gLeft) φ gLeft +
        smoothGiantLogNormalizer (smoothGiantPrimeRange gRight) φ gRight)) *
        (diagonalOuterMajorant Bφ Dφ false * (2 * V n + 1 : ℕ) * Real.exp 2 * E) := by
  apply smoothGiantExternalAverage_full_cell_bound ν (V n) φ gLeft gRight _ hout
  intro i j
  rw [movingPrimeCore_interval_eq]
  have hb := movingOriginalPrimeStatistic_upper q value outside μ ν childBound pivotBound V
    f g Dq S ψ X lo hi φ hφ Bφ Dφ hBφ hDφ hφnorm hlip hout G n m small slot hsmall
    hν hmass hidentical greg ggiant favorable gLeft gRight false
    (if i then gLeft else gLeft - 1) ((if i then gLeft else gLeft - 1) + 1)
    (if j then gRight else gRight - 1) ((if j then gRight else gRight - 1) + 1)
    (if i then gLeft else gLeft - 1) (le_refl _) (le_refl _) E hE (henergy i j)
  simpa only [sub_self, Real.exp_zero, one_pow, one_mul] using hb

end Ostmann

end OAI
