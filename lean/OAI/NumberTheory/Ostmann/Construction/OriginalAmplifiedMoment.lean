import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplificationBudget
import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicWeightPoisson
import OAI.NumberTheory.Ostmann.Construction.AmplifiedRepeatRemoval

namespace OAI

/-! # The original positive amplified moment and distinct-prime lower bound -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform

theorem eventual_physical_amplification_lower (cψ a c : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      0 < P.card → ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ),
      0 < X → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k : ℕ, Even k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) ≤
        ∑' n : ℤ, physicalWeight Q D ψ X n *
          ternaryMean (fun p : P => orientedQuadraticValue ε t n p) ^ k := by
  filter_upwards [eventual_physical_amplification_factor (cψ * a) c (mul_pos hcψ ha) hc,
    eventually_ge_atTop (1 : ℝ)] with T hf hT
  intro Q P hQ hP D ψ X hX hψ0 hψ1 S hS hcard hD hSD ε t hε hbias k heven hk hK
  have hm := physical_moment_from_tail_bias Q P hQ hP D ψ X cψ c hX hcψ.le hc.le
    hψ0 hψ1 S hS hD hSD ε t hε hbias k heven
  have hnum := mul_le_mul_of_nonneg_left (hf k Q.card hk hK) (Real.sqrt_nonneg X)
  calc
    _ ≤ Real.sqrt X * ((cψ * a) * Real.exp ((Q.card : ℝ) / 50) * c ^ k / T ^ 6) := hnum
    _ = (cψ * Real.exp ((Q.card : ℝ) / 50)) * (a * Real.sqrt X / T ^ 6) * c ^ k := by ring
    _ ≤ (cψ * Real.exp ((Q.card : ℝ) / 50)) * S.card * c ^ k := by gcongr
    _ ≤ _ := hm

/-- Combining the physical amplification, the exact total-weight Poisson
identity and the derived repeat-removal estimate. -/
theorem eventual_original_distinct_moment (cψ a c C : ℝ)
    (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c) (hC : 1 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ),
      0 < X → (∀ x, 0 ≤ (ψ x).re) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re) →
      H < X / Q.toList.prod → (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (𝓕 ψ 0).re ≤ C →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k : ℕ, 0 < k → Even k → k ≤ P.card →
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      Real.exp T ≤ C * T * P.card → X ≤ Real.exp ((k : ℝ) * T) →
      Real.sqrt X * Real.exp ((2 / 125 : ℝ) * Q.card) / 2 ≤
        ∑' n : ℤ, physicalWeight Q D ψ X n *
          ternaryDistinctMean (fun p : P => orientedQuadraticValue ε t n p) k := by
  filter_upwards [eventual_physical_amplification_lower cψ a c hcψ ha hc,
    eventual_amplified_repeat_removal C hC] with T hamp hrep
  intro Q P hQ D ψ X H hX hψ0 hψ1 hH hsupp hCψ S hS hcard hD hSD
    ε t hε hbias k hk heven hkP hkU hK hpop hXk
  have hP : 0 < P.card := lt_of_lt_of_le hk hkP
  have hm := hamp Q P hQ hP D ψ X hX hψ0 hψ1 S hS hcard hD hSD ε t hε hbias k heven hkU hK
  have hweight : (∑' n, physicalWeight Q D ψ X n) ≤ C * X := by
    rw [amplification_total_weight Q hQ D ψ X H hX hH hsupp]
    nlinarith only [mul_le_mul_of_nonneg_left hCψ hX.le]
  have hd := hrep (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p) k Q.card X
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n p => orientedQuadraticValue_ternary ε t n p (hε p p.property))
    (physicalWeight_summable Q hQ D ψ X hX) hk heven (by simpa using hkP)
    hkU hK hX (by simpa using hpop) hXk hweight hm
  exact (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 2)).trans hd

end Ostmann

end OAI
