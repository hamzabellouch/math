import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiantDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicKeyMass

namespace OAI

/-! # The single-giant diagonal with its original harmonic mass -/

namespace Ostmann
open scoped Classical BigOperators

/-- Distinctness is forced by the coefficient, rather than imposed on the
sampling law. The harmonic fibre estimate therefore applies without changing
either the original diagonal or its single-branch energy. -/
theorem movingOneGiant_harmonic_diagonal_le {A I : Type*} [Fintype A] [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → I → P) (v : A → ℤ) (μ : A → ℝ) (W : A → ℂ)
    (hμ : ∀ a, 0 ≤ μ a) (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hrow : ∀ a b, X a = X b → y a = y b → v a = v b → a = b)
    (hpoint : ∀ a, μ a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i))
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (y a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, (μ a : ℂ) * W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < (y a i : ℕ))
    (hsep : ∀ a b, (μ a : ℂ) * W a ≠ 0 → (μ b : ℂ) * W b ≠ 0 →
      ∀ i, X a ≠ (y b i : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (μ a : ℂ) * W a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, μ a * θ (X a, (∏ i, (y a i : ℕ)), v a) *
        ‖W a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
  let μ' := fun a => if Function.Injective (y a) then μ a else 0
  let θ := fun k : ℕ × ℕ × ℤ => g k.1 * ((Fintype.card I).factorial : ℝ) *
    (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹
  have hμ' a : 0 ≤ μ' a := by
    dsimp only [μ']
    split_ifs
    · exact hμ a
    · exact le_rfl
  have he a : (μ' a : ℂ) * W a = (μ a : ℂ) * W a := by
    by_cases hi : Function.Injective (y a)
    · simp only [μ', ite_eq_left hi]
    · have hz : (μ a : ℂ) * W a = 0 := by
        by_contra h
        exact hi (hinj a h)
      simp only [μ', ite_eq_right hi, Complex.ofReal_zero, zero_mul, hz]
  have hmass k : (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ' a else 0) ≤ θ k := by
    apply indexed_harmonic_key_mass P hP Q X y v μ' g hg hrow
    · intro a ha
      by_contra hi
      simp only [μ', ite_eq_right hi, ne_eq, not_true_eq_false] at ha
    · intro a _
      by_cases hi : Function.Injective (y a)
      · simpa only [μ', ite_eq_left hi] using hpoint a
      · simp only [μ', ite_eq_right hi]
        exact mul_nonneg (hg _) (Finset.prod_nonneg
          (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have ht := movingOneGiant_weighted_pivot_diagonal_le X (fun a i => (y a i : ℕ))
    greg ggiant favorable D v μ' W θ hμ'
    (fun a ha i j hij => hinj a (by simpa only [he] using ha) (Subtype.ext hij))
    (fun a ha => hv a (by simpa only [he] using ha))
    (fun a ha => hvg a (by simpa only [he] using ha))
    (fun a ha => hvr a (by simpa only [he] using ha))
    (fun a b ha hb => hsep a b (by simpa only [he] using ha) (by simpa only [he] using hb)) hmass
  simp only [he] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : Function.Injective (y a)
  · simp only [μ', ite_eq_left hi, θ]
  · have hz : (μ a : ℂ) * W a = 0 := by
      by_contra h
      exact hi (hinj a h)
    rcases mul_eq_zero.mp hz with hm | hW
    · have hm' : μ a = 0 := by exact_mod_cast hm
      simp only [μ', ite_eq_right hi, hm', zero_mul]
    · simp only [μ', ite_eq_right hi, hW, zero_mul, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]

end Ostmann

end OAI
