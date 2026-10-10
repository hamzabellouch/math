import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticQuadraticCoefficient
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorCoefficientError
import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterDivisorGrid

namespace OAI

/-! # Simultaneous discretization of the full arithmetic coefficient array -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_arithmetic_coefficient_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
          (M h₀ P s : ℕ),
          (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
          (Q.toList.prod : ℝ) ≤ Real.exp T →
          0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
          1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
            arithmeticQuadraticCoefficient Q hQ D Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) P M h₀
              (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ Real.exp (-127 * T) ∧
          ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
            ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s -
              primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
                Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod P U s‖ ≤
              Real.exp (-128 * T) := by
  filter_upwards [eventual_uniform_outer_divisor_grid H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hg hT
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, hpoint⟩ := hg θ R hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, ?_⟩
  intro Q hQ D M h₀ P s hcard hlarge hL hP hPU hs hsU
  have hterm : ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s -
        primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
          Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod P U s‖ ≤
        Real.exp (-128 * T) := by
    intro V hV U hU
    have hUQ := Finset.mem_powerset.mp hU
    have hVQ := Finset.mem_powerset.mp hV
    have hpU : ∀ p ∈ U, p.Prime := fun p hp => hQ p (hUQ hp)
    have hqpos : 0 < U.toList.prod := prime_list_prod_pos _ (primeSet_list_prime U hpU)
    have hvpos : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    let : NeZero U.toList.prod := ⟨hqpos.ne'⟩
    let g := densityFourier (densityCRTList U.toList (primeSet_list_prime U hpU)
      (primeSet_list_coprime U hpU) D).value
    have hqU : (U.toList.prod : ℝ) ≤ Real.exp T := by
      apply le_trans _ hL
      exact_mod_cast primeSet_prod_le_of_subset Q U hQ hUQ
    have hvU : (V.toList.prod : ℝ) ≤ Real.exp T := by
      apply le_trans _ hL
      exact_mod_cast primeSet_prod_le_of_subset Q V hQ hVQ
    have hgq : ∀ x, ‖g x‖ ≤ (U.toList.prod : ℝ) := by
      intro x
      have henergy := densityCRTList_energy U.toList (primeSet_list_prime U hpU)
        (primeSet_list_coprime U hpU) D
      have hh : ‖g x‖ ^ 2 ≤ (U.toList.prod : ℝ) :=
        (Finset.single_le_sum (fun y _ => sq_nonneg ‖g y‖) (Finset.mem_univ x)).trans henergy
      apply (Real.le_sqrt_of_sq_le hh).trans
      exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hqpos))
    have hh := hpoint U.toList.prod s P g U.toList.prod (divisorQuadraticScalar (quadraticInverseResidue M) V U)
      V.toList.prod h₀ hgq hqpos hqU hs hsU hP hPU
      (by exact_mod_cast hvpos) hvU (Nat.cast_nonneg _) hqU
    rw [positiveQuadraticMultiples_eq g _ _ Φ R V.toList.prod s P hP (by linarith)
        (by positivity),
      positiveQuadraticMultiples_eq g _ _ Φ _ V.toList.prod s P hP (by linarith)
        (by positivity)] at hh
    simpa only [primeDivisorMultiples, primeDivisorPositive, dite_eq_left hUQ] using hh
  refine ⟨?_, hterm⟩
  apply (fullQuadraticCoefficient_difference_bound Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ)
    (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
    Φ R (quadraticGridScale (Real.exp (-200 * T)) j) P
    (quadraticSymbolCoefficient M) (quadraticDivisorSymbol M) s
    (Real.exp (-128 * T)) (Real.exp_nonneg _)
    (fun U _ => quadraticSymbolCoefficient_norm_le M U)
    (fun V _ => quadraticDivisorSymbol_norm_le M V) hterm).trans
      (full_coefficient_grid_error_budget Q T hT hcard hlarge)

end Ostmann

end OAI
