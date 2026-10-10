import OAI.NumberTheory.DukePrimeDegree.Geometry.RepeatedRoot
import OAI.NumberTheory.DukePrimeDegree.Geometry.SpectralSeparation

namespace OAI

/-!
# A scalar double block in an integral return matrix

The centralizer of the root SL₂ has a scalar two-dimensional block.
The remaining block in a sufficiently separated return has simple real
spectrum. Such a return matrix cannot be conjugate to an integral
special-linear matrix unless the scalar eigenvalue is ±1.
-/

noncomputable section
open Polynomial Matrix
open scoped Classical

namespace DukePrimeDegree

lemma double_factor_unique_repeated_root
    {K : Type*} [Field K] (q : K[X]) (hq : q ≠ 0) (hsep : q.Separable) (c : K) :
    1 < ((X - C c) ^ 2 * q).rootMultiplicity c ∧
      ∀ y : K, 1 < ((X - C c) ^ 2 * q).rootMultiplicity y → y = c := by
  constructor
  · rw [mul_comm, rootMultiplicity_mul_X_sub_C_pow hq]
    omega
  · intro y hy
    by_contra hne
    have hn : (X - C c) ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero c)) hq
    rw [rootMultiplicity_mul hn] at hy
    have hnot : ¬ ((X - C c) ^ 2 : K[X]).IsRoot y := by
      simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
        sub_eq_zero]
      exact hne
    rw [rootMultiplicity_eq_zero hnot, zero_add] at hy
    exact (not_lt_of_ge (rootMultiplicity_le_one_of_separable hsep y)) hy

/-- The arithmetic obstruction only needs a scalar double factor and a
separable residual polynomial, not a complete eigenbasis. -/
theorem integer_unit_polynomial_double_factor
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0))
    (c : ℝ) (q : ℝ[X]) (hq : q.Monic) (hsep : q.Separable)
    (hfactor : p.map (algebraMap ℤ ℝ) = (X - C c) ^ 2 * q) :
    c = 1 ∨ c = -1 := by
  have hfactorC : p.map (algebraMap ℤ ℂ) =
      (X - C (c : ℂ)) ^ 2 * q.map (algebraMap ℝ ℂ) := by
    have h := congrArg (fun r : ℝ[X] => r.map (algebraMap ℝ ℂ)) hfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℝ ℂ,
      Complex.coe_algebraMap] using h
  have hqC : q.map (algebraMap ℝ ℂ) ≠ 0 := (hq.map _).ne_zero
  have hsepC : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  obtain ⟨hcroot, hunique⟩ := double_factor_unique_repeated_root
    (q.map (algebraMap ℝ ℂ)) hqC hsepC (c : ℂ)
  rw [← hfactorC] at hcroot hunique
  rcases unique_repeated_root_of_monic_unit_constant p hp hc (c : ℂ) hcroot hunique with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- No integral special-linear return can have a nonunit scalar double
block and a separable complementary characteristic factor. -/
theorem integer_sl_double_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix.SpecialLinearGroup ι ℤ)
    (c : ℝ) (q : ℝ[X]) (hq : q.Monic) (hsep : q.Separable)
    (hfactor : g.val.charpoly.map (algebraMap ℤ ℝ) = (X - C c) ^ 2 * q) :
    c = 1 ∨ c = -1 := by
  apply integer_unit_polynomial_double_factor g.val.charpoly g.val.charpoly_monic _ c q hq hsep hfactor
  apply isUnit_of_dvd_one
  refine ⟨(-1 : ℤ) ^ Fintype.card ι, ?_⟩
  have h := g.val.det_eq_sign_charpoly_coeff
  rw [g.property] at h
  simpa only [mul_comm] using h

/-- The matrix form of the double-factor obstruction, invariant under a real
change of basis. -/
theorem integer_sl_scalar_double_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix.SpecialLinearGroup (Fin 2 ⊕ ι) ℤ)
    (P : Matrix.SpecialLinearGroup (Fin 2 ⊕ ι) ℝ)
    (c : ℝ) (B : Matrix ι ι ℝ) (hsep : B.charpoly.Separable)
    (hblock : P.val * g.val.map (algebraMap ℤ ℝ) * (P⁻¹).val =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B) :
    c = 1 ∨ c = -1 := by
  have hcancel : (P⁻¹).val * P.val = 1 := by
    change (P⁻¹ * P).val = 1
    simp
  have hpoly : g.val.charpoly.map (algebraMap ℤ ℝ) =
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B).charpoly := by
    rw [← Matrix.charpoly_map]
    have heq := congrArg Matrix.charpoly hblock
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hcancel, one_mul] at heq
    exact heq
  apply integer_sl_double_factor g c B.charpoly B.charpoly_monic hsep
  rw [hpoly, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  simp [pow_two]

/-- A sufficiently small return with separated complementary weights cannot
be integral up to conjugacy when its scalar double block is not a unit. -/
theorem no_integral_scalar_double_return {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix.SpecialLinearGroup (Fin 2 ⊕ ι) ℤ)
    (P : Matrix.SpecialLinearGroup (Fin 2 ⊕ ι) ℝ)
    (c : ℝ) (hc : c ≠ 1 ∧ c ≠ -1)
    (ell : ι → ℝ) (hgap : ∀ i j, i ≠ j → 1 < |ell i - ell j|)
    (H : Matrix ι ι ℝ)
    (hH : ∀ i, ∑ j, ‖(H - 1) i j‖ < spectralRelativeRadius)
    (hblock : P.val * g.val.map (algebraMap ℤ ℝ) * (P⁻¹).val =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0
        (H * Matrix.diagonal (fun j => Real.exp (ell j)))) : False := by
  obtain ⟨_, _, _, _, _, hsep⟩ := real_spectrum_of_logarithmic_gaps ell hgap H hH
  exact (integer_sl_scalar_double_block g P c _ hsep hblock).elim hc.1 hc.2

end DukePrimeDegree

end

end OAI
