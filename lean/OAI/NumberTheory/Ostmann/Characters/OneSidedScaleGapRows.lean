import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationData
import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinear

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap
variable {η κ σ τ : Type*} [Fintype η] [Fintype κ] [Fintype σ] [Fintype τ]

omit [Fintype κ] in
theorem characterGram_polynomial_rows_bound [Fintype κ]
    (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ) (hq : ∀ j, (q j).Prime)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : η → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (b : η → ℕ → ℝ) (W : η → ℕ → κ → ℂ) (j k : κ) (hjk : q j ≠ q k)
    (data : η → HistoryPolynomialData σ τ) (A B : η → τ → ℝ) (M : η → ℝ)
    (hdata : ∀ r, (data r).Ranges ρ (A r) (B r) (M r))
    (c : ℂ)
    (heq : ∀ r n, n ≤ N → crossProgressionWeight (b r) (W r) j k n =
      c*(data r).weight ρ ((Q*n+a r : ℕ) : ℝ)) :
    ‖oneSidedGram (fun x : η × Fin N => b x.1 x.2)
      (rowCharacterKernel q χ Q N a W) j k‖ ≤
      ((q j*q k : ℕ) : ℝ) * ‖c‖ * ∑ r, (data r).variationCost (A r) (B r) (M r) := by
  rw [oneSidedGram_rows_eq]
  calc
    _ ≤ ∑ r, ‖oneSidedGram (fun n : Fin N => b r n)
        (fun n : Fin N => primeCharacterKernel q χ Q (a r) (W r) n) j k‖ := norm_sum_le _ _
    _ ≤ ∑ r, ((q j*q k : ℕ) : ℝ) * (‖c‖*(data r).variationCost (A r) (B r) (M r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact (characterGram_bound q hq χ hχ Q (a r) N hQ (b r) (W r) j k hjk).trans
        (mul_le_mul_of_nonneg_left
          ((data r).scaled_progressionVariation_le ρ (hdata r) Q (a r) N c _ (heq r))
          (Nat.cast_nonneg _))
    _ = _ := by simp_rw [← mul_assoc]; rw [← Finset.mul_sum]

theorem characterGram_polynomial_rows_uniform
    (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ) (hq : ∀ j, (q j).Prime)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : η → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (b : η → ℕ → ℝ) (W : η → ℕ → κ → ℂ) (j k : κ) (hjk : q j ≠ q k)
    (data : η → HistoryPolynomialData σ τ) (A B : η → τ → ℝ) (M : η → ℝ)
    (hdata : ∀ r, (data r).Ranges ρ (A r) (B r) (M r))
    (c : ℂ)
    (heq : ∀ r n, n ≤ N → crossProgressionWeight (b r) (W r) j k n =
      c*(data r).weight ρ ((Q*n+a r : ℕ) : ℝ))
    {P D : ℝ} (hP : 0 ≤ P) (_hD : 0 ≤ D)
    (hprime : ∀ i, (q i : ℝ) ≤ P)
    (hcost : ∀ r, (data r).variationCost (A r) (B r) (M r) ≤ D) :
    ‖oneSidedGram (fun x : η × Fin N => b x.1 x.2)
      (rowCharacterKernel q χ Q N a W) j k‖ ≤
      (Fintype.card η : ℝ)*P^2*‖c‖*D := by
  apply (characterGram_polynomial_rows_bound ρ q hq χ hχ Q N a hQ b W j k hjk
    data A B M hdata c heq).trans
  have hqs : ((q j*q k : ℕ) : ℝ) ≤ P^2 := by
    rw [Nat.cast_mul,pow_two]
    exact mul_le_mul (hprime j) (hprime k) (Nat.cast_nonneg _) hP
  have hs : (∑ r, (data r).variationCost (A r) (B r) (M r)) ≤
      (Fintype.card η : ℝ)*D := by
    simpa using Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hcost r)
  have hs0 : 0 ≤ ∑ r, (data r).variationCost (A r) (B r) (M r) :=
    Finset.sum_nonneg (fun r _ => (data r).variationCost_nonneg ρ (hdata r))
  calc
    _ ≤ (P^2*‖c‖)*((Fintype.card η : ℝ)*D) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hqs (norm_nonneg _)) hs hs0
        (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end Ostmann.Characters

end

end OAI
