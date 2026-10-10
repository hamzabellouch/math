import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapRows

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable

private theorem prior_cross_sum_le {κ : Type*} [Fintype κ]
    (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j) (hmass : ∑ j, ν j ≤ 1)
    (G : κ → κ → ℝ) {R : ℝ} (hR : 0 ≤ R) (hG : ∀ j k, j ≠ k → G j k ≤ R) :
    (∑ j, ∑ k, if j=k then 0 else ν j*ν k*G j k) ≤ R := by
  have hs0 : 0 ≤ ∑ j, ν j := Finset.sum_nonneg (fun j _ => hν j)
  calc
    _ ≤ ∑ j, ∑ k, ν j*ν k*R := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      split_ifs with h
      · exact mul_nonneg (mul_nonneg (hν j) (hν k)) hR
      · exact mul_le_mul_of_nonneg_left (hG j k h) (mul_nonneg (hν j) (hν k))
    _ = (∑ j, ν j)*(∑ j, ν j)*R := by simp only [Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hmass hs0,
      mul_le_mul_of_nonneg_right hmass hR,
      mul_le_mul_of_nonneg_right (mul_le_mul hmass hmass hs0 (by norm_num : (0:ℝ)≤1)) hR]

theorem oneSided_bilinear_profile_bound
    {η κ σ τ : Type*} [Fintype η] [Fintype κ] [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : η → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (μ : η × Fin N → ℝ) (b : η → ℕ → ℝ) (ν : κ → ℝ)
    (U : η × Fin N → ℂ) (V : κ → ℂ) (W : η → ℕ → κ → ℂ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x ≤ 1)
    (hmajorant : ∀ x : η × Fin N, μ x ≤ b x.1 x.2)
    (hν : ∀ j, 0 ≤ ν j) (hνmass : ∑ j, ν j ≤ 1)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1)
    (data : η → κ → κ → HistoryPolynomialData σ τ)
    (A B : τ → ℝ) (M : ℝ) (c : ℂ)
    (hdata : ∀ r j k, j ≠ k → (data r j k).Ranges ρ A B M)
    (heq : ∀ r j k, j ≠ k → ∀ n, n ≤ N →
      crossProgressionWeight (b r) (W r) j k n = c*(data r j k).weight ρ ((Q*n+a r : ℕ) : ℝ))
    {P D : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hprime : ∀ j, (q j : ℝ) ≤ P)
    (hcost : ∀ r j k, j ≠ k → (data r j k).variationCost A B M ≤ D) :
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a W)‖^2 ≤
      priorMaxAtom ν * oneSidedWeightEnergy N b ν W +
        (Fintype.card η : ℝ)*P^2*‖c‖*D := by
  have hb (x : η × Fin N) : 0 ≤ b x.1 x.2 := (hμ x).trans (hmajorant x)
  have hmax : 0 ≤ priorMaxAtom ν := by unfold priorMaxAtom; positivity
  apply (oneSided_bilinear_gram_bound μ (fun x : η × Fin N => b x.1 x.2)
    ν U V (rowCharacterKernel q χ Q N a W) hμ hmass hmajorant hν hU hV).trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hmax
    unfold oneSidedWeightEnergy
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hν j)
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (hb x)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    let : Fact (q j).Prime := ⟨hq j⟩
    unfold rowCharacterKernel primeCharacterKernel
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_character_le_one (χ j) _) (norm_nonneg (W x.1 x.2 j))
  · apply prior_cross_sum_le ν hν hνmass _ (by positivity)
    intro j k hjk
    exact characterGram_polynomial_rows_uniform ρ q hq χ hχ Q N a hQ b W j k
      (fun h => hjk (hinj h)) (fun r => data r j k) (fun _ => A) (fun _ => B)
      (fun _ => M) (fun r => hdata r j k hjk) c (fun r => heq r j k hjk)
      hP hD hprime (fun r => hcost r j k hjk)

end Ostmann.Characters

end

end OAI
