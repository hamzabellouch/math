import OAI.Probability.ClassicalON.FourierOperator

namespace OAI

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

theorem restricted_modulated_fourier_bound {X : Type uX} {P : Type uP} {Y : Type uY}
    [Fintype X] [Fintype P] [Fintype Y] [DecidableEq P]
    (W : X → P → ℂ) (M C A : ℝ) (hM : 0 ≤ M)
    (hW : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (i : Y → X) (hi : Function.Injective i) (d : Y → ℂ) (a v : P → ℂ)
    (hd : ∀ y, ‖d y‖ ≤ C) (ha : ∀ p, ‖a p‖ ≤ A) :
    (∑ y, ‖d y*(∑ p, W (i y) p*(a p*v p))‖^2) ≤ (C^2*M*A^2)*∑ p, ‖v p‖^2 := by
  calc _ ≤ C^2*∑ y, ‖∑ p, W (i y) p*(a p*v p)‖^2 := sum_norm_pointwise_mul_sq_le _ _ C hd
       _ ≤ C^2*∑ x, ‖∑ p, W x p*(a p*v p)‖^2 :=
          mul_le_mul_of_nonneg_left (sum_norm_sq_restrict i hi (fun x => ∑ p, W x p*(a p*v p))) (sq_nonneg _)
       _ ≤ C^2*((M*A^2)*∑ p, ‖v p‖^2) := mul_le_mul_of_nonneg_left
          (parseval_diagonal_bound W M A hM hW a v ha) (sq_nonneg _)
       _ = _ := by ring

theorem edge_cutoff_squareBound {P : Type uP} {Y : Type uY} [Fintype P] [Fintype Y] [DecidableEq P]
    {L : ℕ} [NeZero L] (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (i : Y → DiscreteTorus L) (hi : Function.Injective i) (h : DiscreteTorus L)
    (φ₀ φ₁ : Y → ℂ) (a : P → ℂ)
    (D C A B : ℝ) (hD : ∀ y, ‖φ₁ y-φ₀ y‖ ≤ D) (hC : ∀ y, ‖φ₁ y‖ ≤ C)
    (hA : ∀ q, ‖a q‖ ≤ A) (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    SquareBound (fun y q => a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y)))
      (Real.sqrt (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))) := by
  intro v
  rw [Real.sq_sqrt (by positivity)]
  let f := fun y => (φ₁ y-φ₀ y)*(∑ q, torusWave (p q) (i y)*(a q*v q))
  let g := fun y => φ₁ y*(∑ q, torusWave (p q) (i y)*((a q*(torusWave (p q) h-1))*v q))
  have he (y : Y) :
      (∑ q, a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y))*v q) = f y+g y := by
    simp only [f, g, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [torusWave_add]
    ring
  simp_rw [he]
  have hf := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) D A
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi (fun y => φ₁ y-φ₀ y) a v hD hA
  have hg := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) C B
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi φ₁ (fun q => a q*(torusWave (p q) h-1)) v hC hB
  have ht := sum_norm_add_sq_le f g
  dsimp only [f, g] at ht ⊢
  linarith

end ClassicalON

end

end OAI
