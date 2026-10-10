import OAI.Probability.ClassicalON.MatrixSquare

namespace OAI

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {X : Type uX} {P : Type uP} {Y : Type uY} [Fintype X] [Fintype P] [Fintype Y]

theorem sum_norm_pointwise_mul_sq_le (d v : X → ℂ) (c : ℝ) (hd : ∀ x, ‖d x‖ ≤ c) :
    (∑ x, ‖d x*v x‖^2) ≤ c^2*∑ x, ‖v x‖^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd x) 2) (sq_nonneg _)

theorem sum_norm_sq_restrict (i : Y → X) (hi : Function.Injective i) (v : X → ℂ) :
    (∑ y, ‖v (i y)‖^2) ≤ ∑ x, ‖v x‖^2 := by
  classical
  calc _ = ∑ x ∈ Finset.univ.image i, ‖v x‖^2 := (Finset.sum_image (fun a _ b _ h => hi h)).symm
       _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg _

theorem modulated_fourier_bound [DecidableEq P] (W : X → P → ℂ) (M C A : ℝ)
    (hM : 0 ≤ M)
    (hW : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (d : X → ℂ) (a v : P → ℂ) (hd : ∀ x, ‖d x‖ ≤ C) (ha : ∀ p, ‖a p‖ ≤ A) :
    (∑ x, ‖d x*(∑ p, W x p*(a p*v p))‖^2) ≤ (C^2*M*A^2)*∑ p, ‖v p‖^2 := by
  calc _ ≤ C^2*∑ x, ‖∑ p, W x p*(a p*v p)‖^2 := sum_norm_pointwise_mul_sq_le _ _ C hd
       _ ≤ C^2*((M*A^2)*∑ p, ‖v p‖^2) := mul_le_mul_of_nonneg_left
          (parseval_diagonal_bound W M A hM hW a v ha) (sq_nonneg _)
       _ = _ := by ring

theorem cutoff_fourier_difference_bound {L : ℕ} [NeZero L] [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (φ : DiscreteTorus L → ℂ) (h : DiscreteTorus L) (a v : P → ℂ)
    (D C A B : ℝ) (hD : ∀ x, ‖φ (x+h)-φ x‖ ≤ D)
    (hC : ∀ x, ‖φ (x+h)‖ ≤ C) (hA : ∀ q, ‖a q‖ ≤ A)
    (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    (∑ x, ‖∑ q, (a q*(φ (x+h)*torusWave (p q) (x+h)-φ x*torusWave (p q) x))*v q‖^2) ≤
      (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))*∑ q, ‖v q‖^2 := by
  let f := fun x => (φ (x+h)-φ x)*(∑ q, torusWave (p q) x*(a q*v q))
  let g := fun x => φ (x+h)*(∑ q, torusWave (p q) x*((a q*(torusWave (p q) h-1))*v q))
  have he (x : DiscreteTorus L) :
      (∑ q, a q*(φ (x+h)*torusWave (p q) (x+h)-φ x*torusWave (p q) x)*v q) = f x+g x := by
    simp only [f, g, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [torus_mode_difference]
    ring
  simp_rw [he]
  have hf := modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) D A
    (sq_nonneg _) (fun i j => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp i j) (fun x => φ (x+h)-φ x) a v hD hA
  have hg := modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) C B
    (sq_nonneg _) (fun i j => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp i j) (fun x => φ (x+h))
    (fun q => a q*(torusWave (p q) h-1)) v hC hB
  have ht := sum_norm_add_sq_le f g
  dsimp only [f, g] at ht ⊢
  linarith

theorem restricted_cutoff_squareBound {L : ℕ} [NeZero L] [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (φ : DiscreteTorus L → ℂ) (h : DiscreteTorus L) (a : P → ℂ)
    (i : Y → DiscreteTorus L) (hi : Function.Injective i)
    (D C A B : ℝ) (hD : ∀ x, ‖φ (x+h)-φ x‖ ≤ D)
    (hC : ∀ x, ‖φ (x+h)‖ ≤ C) (hA : ∀ q, ‖a q‖ ≤ A)
    (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    SquareBound (fun y q => a q*(φ (i y+h)*torusWave (p q) (i y+h)-φ (i y)*torusWave (p q) (i y)))
      (Real.sqrt (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))) := by
  intro v
  rw [Real.sq_sqrt (by positivity)]
  exact (sum_norm_sq_restrict i hi _).trans
    (cutoff_fourier_difference_bound p hp φ h a v D C A B hD hC hA hB)

end ClassicalON

end

end OAI
