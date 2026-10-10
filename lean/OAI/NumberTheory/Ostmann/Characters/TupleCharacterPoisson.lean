import Mathlib.NumberTheory.DirichletCharacter.Bounds
import OAI.NumberTheory.Ostmann.Characters.TupleCRTFourier
import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicWeightPoisson

namespace OAI

/-! # Poisson summation and the initial graph phase of a character tuple -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap ComplexConjugate Classical

noncomputable def primitiveGaussPhase {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) : ℂ :=
  gaussSum χ ZMod.stdAddChar / (Real.sqrt (p : ℝ) : ℂ)

theorem primitiveGaussPhase_norm {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖primitiveGaussPhase χ‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hg := primitive_gauss_norm_sq χ hχ
  have he : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (p : ℝ),
      norm_nonneg (gaussSum χ ZMod.stdAddChar)]
  rw [primitiveGaussPhase, norm_div, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

theorem inverse_character_inverse_unit {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (hx : IsUnit x) : χ⁻¹ x⁻¹ = χ x := by
  obtain ⟨u, rfl⟩ := hx
  have h := MulChar.inv_apply χ⁻¹ (u : ZMod p)
  rw [inv_inv, Ring.inverse_unit] at h
  simpa only [ZMod.inv_coe_unit] using h.symm

noncomputable def tupleGraphPhase {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
    primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i)) *
      ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i))

/-- Each off-diagonal edge has exponent one at level zero, including the
inverse characters assigned to conjugate slots. -/
theorem tuple_character_fourier {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    additiveFourier (tupleCRTFunction p hc (fun i x => χ i (x - t i))) (-(v : ZMod (∏ i, p i))) =
      (Real.sqrt (∏ i, p i : ℕ) : ℂ)⁻¹ * tupleGraphPhase p χ t v := by
  rw [tupleCRTFunction_fourier]
  have hi (i : I) :
      additiveFourier (fun x => χ i (x - t i))
        ((tupleCofactor p i : ZMod (p i))⁻¹ *
          ZMod.prodEquivPi p hc (-(v : ZMod (∏ i, p i))) i) =
      (Real.sqrt (p i : ℝ) : ℂ)⁻¹ *
        (ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
          primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i)) *
            ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i))) := by
    simp only [map_neg, map_intCast, Pi.neg_apply, Pi.intCast_apply, mul_neg]
    rw [additiveFourier_translate, primitive_character_fourier (χ i) (hχ i)]
    simp only [neg_neg, mul_neg]
    rw [map_mul ((χ i)⁻¹), inverse_character_inverse_unit (χ i) _
      ((ZMod.isUnit_iff_coprime _ _).mpr (tupleCofactor_coprime p hc i))]
    have he : χ i (tupleCofactor p i : ZMod (p i)) =
        ∏ j ∈ Finset.univ.erase i, χ i (p j : ZMod (p i)) := by
      simp only [tupleCofactor, Nat.cast_prod, map_prod]
    rw [he]
    have hs : (Real.sqrt (p i : ℝ) : ℂ) ^ 2 = p i := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (p i))
    have hsp : (Real.sqrt (p i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p i by exact_mod_cast NeZero.pos (p i))).ne'
    have hpC : (p i : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (p i)
    unfold primitiveGaussPhase
    field_simp [hpC]
    rw [hs]
    ring
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  have hs : (Real.sqrt (∏ i, p i : ℕ) : ℂ) = ∏ i, (Real.sqrt (p i : ℝ) : ℂ) := by
    rw [Nat.cast_prod, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i)), Complex.ofReal_prod]
  rw [hs, Finset.prod_inv_distrib]
  rfl

theorem tuple_character_poisson {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) =
      ((X : ℂ) / (Real.sqrt (∏ i, p i : ℕ) : ℂ)) *
        ∑' v : ℤ, 𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  have hp := scaled_periodic_poisson (tupleCRTFunction p hc (fun i x => χ i (x - t i))) ψ X hX
  simp_rw [tupleCRTFunction_intCast, tuple_character_fourier p hc χ hχ t] at hp
  rw [hp, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro v
  ring

theorem tupleGraphPhase_norm_le_one {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (hχ : ∀ i, (χ i).IsPrimitive) (t : ∀ i, ZMod (p i)) (v : ℤ) :
    ‖tupleGraphPhase p χ t v‖ ≤ 1 := by
  rw [tupleGraphPhase, norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe,
    primitiveGaussPhase_norm (χ i) (hχ i), one_mul, norm_prod]
  have hb := Finset.prod_le_one₀ (fun j _ => norm_nonneg (χ i (p j : ZMod (p i))))
    (fun j _ => (χ i).norm_le_one (p j : ZMod (p i))) (s := Finset.univ.erase i)
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
    (by simpa only [mul_one] using ((χ i)⁻¹).norm_le_one (v : ZMod (p i)))

theorem tupleGraphPhase_zero {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) (i : I) (hi : ¬IsUnit (v : ZMod (p i))) :
    tupleGraphPhase p χ t v = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [((χ i)⁻¹).map_nonunit hi, mul_zero, zero_mul]

theorem tuple_character_poisson_normalized {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑' v : ℤ, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  rw [tuple_character_poisson p hc χ hχ t ψ X hX, div_eq_mul_inv, mul_assoc, ← tsum_mul_right,
    ← tsum_mul_left]
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  have hx : (Real.sqrt X : ℂ) ^ 2 = X := by exact_mod_cast Real.sq_sqrt hX.le
  have hx0 : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have hm0 : (Real.sqrt (∏ i, p i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  rw [Real.sqrt_div hX.le]
  push_cast
  apply tsum_congr
  intro v
  field_simp [hx0, hm0]
  rw [hx]
  ring

end Ostmann

end OAI
