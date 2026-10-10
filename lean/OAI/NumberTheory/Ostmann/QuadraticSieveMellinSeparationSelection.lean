import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationSelection
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparation

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

noncomputable def mellinWeightedEnergy (S : Finset ℕ) (a : ℕ → ℂ) (β : ℕ → ℝ) (σ : ℝ) : ℝ :=
  ∑ n ∈ S, ‖a n‖ ^ 2 * ((β n) ^ (-σ)) ^ 2

theorem mellinWeightedEnergy_nonneg (S : Finset ℕ) (a : ℕ → ℂ) (β : ℕ → ℝ) (σ : ℝ) :
    0 ≤ mellinWeightedEnergy S a β σ :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem exists_uniform_mellin_gcd_scales (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ)
      (β γ : ℕ → ℝ) (σ : ℝ),
      d ≠ 0 → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      ∃ d₁ d₂ : ℕ, 0 < d₁ ∧ 0 < d₂ ∧ d₁ * d₂ = d ∧ ∀ r : ℝ,
        (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ^ 2 ≤
          C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
            quadraticNorm V (oddSquarefreeUpTo (N / d₂)) *
            mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ := by
  obtain ⟨C, hC, hsep⟩ := exists_gcd_separation_scales ε hε
  refine ⟨C, hC, ?_⟩
  intro V S T a b d N β γ σ hd hV hS hT hβ hγ
  have hne : d.divisorsAntidiagonal.Nonempty :=
    ⟨(1, d), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul d, hd⟩⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image d.divisorsAntidiagonal
    (fun e => quadraticNorm V (oddSquarefreeUpTo (N / e.1)) *
      quadraticNorm V (oddSquarefreeUpTo (N / e.2))) hne
  have hemul := (Nat.mem_divisorsAntidiagonal.mp he).1
  have he₁ : 0 < e.1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hemul; omega)
  have he₂ : 0 < e.2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hemul; omega)
  refine ⟨e.1, e.2, he₁, he₂, hemul, ?_⟩
  intro r
  obtain ⟨f₁, f₂, hf₁, hf₂, hfprod, hbnd⟩ :=
    hsep V S T (mellinTwist σ r β a) (mellinTwist σ r γ b) d N hd hV hS hT
  rw [coefficientEnergy_mellinTwist S a β σ r hβ,
    coefficientEnergy_mellinTwist T b γ σ r hγ] at hbnd
  have hprod := hmax (f₁, f₂) (Nat.mem_divisorsAntidiagonal.mpr ⟨hfprod, hd⟩)
  apply hbnd.trans
  change C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / f₁)) *
      quadraticNorm V (oddSquarefreeUpTo (N / f₂)) *
      mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ ≤ _
  have hc : 0 ≤ C * (N : ℝ) ^ ε := by positivity
  have henergy : 0 ≤ mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ :=
    mul_nonneg (mellinWeightedEnergy_nonneg _ _ _ _) (mellinWeightedEnergy_nonneg _ _ _ _)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hc) henergy
  simpa only [mul_assoc] using h

end Ostmann.QuadraticSieve

end OAI
