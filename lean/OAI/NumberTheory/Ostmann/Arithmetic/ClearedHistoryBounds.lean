import OAI.NumberTheory.Ostmann.Arithmetic.ClearedHistoryPivot

namespace OAI

/-! # Degree and value control survives clearing every history denominator -/

namespace Ostmann.ClearedHistoryValue

open scoped BigOperators Classical

variable {σ : Type*}

def Bounded (F : ClearedHistoryValue σ) (x : σ → ℝ) (H : ℝ) : Prop :=
  |MvPolynomial.eval₂ (Int.castRingHom ℝ) x F.numerator| ≤ H ∧ |(F.denominator : ℝ)| ≤ H

theorem bounded_variable (i : σ) (x : σ → ℝ) (H : ℝ) (hH : 1 ≤ H) (hx : |x i| ≤ H) :
    (ofVariable i).Bounded x H := by
  exact ⟨by simpa only [Bounded, ofVariable, MvPolynomial.eval₂_X] using hx,
    by simpa only [ofVariable, Int.cast_one, abs_one] using hH⟩

theorem bounded_constant (a : ℤ) (x : σ → ℝ) (H : ℝ) (hH : 1 ≤ H) (ha : |(a : ℝ)| ≤ H) :
    (constant a).Bounded x H := by
  exact ⟨by simpa only [constant, MvPolynomial.eval₂_C, Int.coe_castRingHom] using ha,
    by simpa only [constant, Int.cast_one, abs_one] using hH⟩

theorem bounded_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ)
    (x : σ → ℝ) (H : I → ℝ) (hf : ∀ i ∈ S, (f i).Bounded x (H i)) :
    (prod S f).Bounded x (∏ i ∈ S, H i) := by
  constructor
  · change |MvPolynomial.eval₂ (Int.castRingHom ℝ) x (∏ i ∈ S, (f i).numerator)| ≤ _
    change |(MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x) (∏ i ∈ S, (f i).numerator)| ≤ _
    rw [map_prod, Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i hi => (hf i hi).1)
  · change |((∏ i ∈ S, (f i).denominator : ℤ) : ℝ)| ≤ _
    rw [Int.cast_prod, Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i hi => (hf i hi).2)

/-- No coefficient-height estimate is assumed. The exact two products in the
substitution give a value bound that is valid at every real assignment. -/
theorem bounded_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℝ) (HL HR : ℝ) (hL : left.Bounded x HL) (hR : right.Bounded x HR) :
    (pivot left right v w s hs).Bounded x
      ((|(v : ℝ)| + |(w : ℝ)| + |(s : ℝ)|) * HL * HR) := by
  have hHL : 0 ≤ HL := (abs_nonneg _).trans hL.2
  have hHR : 0 ≤ HR := (abs_nonneg _).trans hR.2
  have hprod : 0 ≤ HL * HR := mul_nonneg hHL hHR
  have hleft : |(v : ℝ) * (left.denominator : ℝ) *
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x right.numerator| ≤ |(v : ℝ)| * HL * HR := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)) hR.1
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hHL)
  have hright : |(w : ℝ) * (right.denominator : ℝ) *
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x left.numerator| ≤ |(w : ℝ)| * HR * HL := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR.2 (abs_nonneg _)) hL.1
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hHR)
  constructor
  · change |MvPolynomial.eval₂ (Int.castRingHom ℝ) x
      (MvPolynomial.C (v * left.denominator) * right.numerator -
        MvPolynomial.C (w * right.denominator) * left.numerator)| ≤ _
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      Int.coe_castRingHom, Int.cast_mul]
    apply (abs_sub _ _).trans
    nlinarith [mul_nonneg (abs_nonneg (s : ℝ)) hprod]
  · change |((s * left.denominator * right.denominator : ℤ) : ℝ)| ≤ _
    rw [Int.cast_mul, Int.cast_mul, abs_mul, abs_mul]
    have hd := mul_le_mul (mul_le_mul_of_nonneg_left hL.2 (abs_nonneg (s : ℝ))) hR.2
      (abs_nonneg (right.denominator : ℝ)) (mul_nonneg (abs_nonneg (s : ℝ)) hHL)
    nlinarith [mul_nonneg (abs_nonneg (v : ℝ)) hprod,
      mul_nonneg (abs_nonneg (w : ℝ)) hprod]

theorem zero_variable_value_bound (F : ClearedHistoryValue σ) (i : σ) (x : σ → ℤ) (H : ℝ)
    (hF : F.Bounded (fun j => ((Function.update x i 0) j : ℝ)) H) :
    |((MvPolynomial.eval₂Hom (RingHom.id ℤ) x
      (zeroHistoryVariable i F.numerator) : ℤ) : ℝ)| ≤ H := by
  rw [zeroHistoryVariable_eval]
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℤ) (Function.update x i 0)
    (Int.castRingHom ℝ) F.numerator
  have he' : ((MvPolynomial.eval₂Hom (RingHom.id ℤ) (Function.update x i 0) F.numerator : ℤ) : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun j => ((Function.update x i 0) j : ℝ)) F.numerator := by
    simpa [Int.castRingHom] using he
  rw [he']
  exact hF.1

end Ostmann.ClearedHistoryValue

end OAI
