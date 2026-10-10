import OAI.NumberTheory.Ostmann.Characters.AmplifiedCharacterPoisson
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleTranslation

namespace OAI

/-! # Transferring each genuine distinct-prime term to positive frequencies -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem ofReal_re_of_conj_eq (z : ℂ) (h : conj z = z) : (z.re : ℂ) = z := by
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  have hz : z.im = 0 := by linarith
  exact Complex.ext (by simp) (by simp [hz])

theorem physical_tuple_jacobi_norm (Q P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (X : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    {k : ℕ} (e : Fin k ↪ P) (tM : ℤ)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val)) :
    |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| =
      ‖∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℂ) * ψ ((n : ℝ) / X)‖ := by
  have hp (n : ℤ) : physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val =
      (∏ i, ε (e i).val) * amplificationWeight Q D n *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℝ) * (ψ ((n : ℝ) / X)).re := by
    simp only [physicalWeight, orientedQuadraticValue, Finset.prod_mul_distrib]
    rw [← jacobi_primeTuple_translation P hP e t tM n ht]
    ring
  have he : (((∑' n : ℤ, physicalWeight Q D ψ X n *
        ∏ i, orientedQuadraticValue ε t n (e i).val) : ℝ) : ℂ) =
      (∏ i, (ε (e i).val : ℂ)) * ∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - tM) (primeTupleProduct P e) : ℂ) * ψ ((n : ℝ) / X) := by
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hp]
    push_cast
    rw [ofReal_re_of_conj_eq _ (hreal _)]
    ring
  have hc : ‖∏ i, (ε (e i).val : ℂ)‖ = 1 := by
    rw [norm_prod]
    have hh (i : Fin k) : ‖(ε (e i).val : ℂ)‖ = 1 := by
      rcases hε _ (e i).property with h | h <;> rw [h] <;> norm_num
    simp only [hh, Finset.prod_const_one]
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hc, one_mul] using congrArg norm he

theorem physical_tuple_positive_bound (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (X H : ℝ) (hX : 0 < X) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (t : ℕ → ℤ)
    {k : ℕ} (hk : 0 < k) (e : Fin k ↪ P)
    (hcop : Q.toList.prod.Coprime (primeTupleProduct P e)) (N h₀ : ℕ)
    (hcut : H * ((primeTupleProduct P e : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0)
    (tM : ℤ) (htM : 0 ≤ tM) (htMlt : tM < primeTupleProduct P e)
    (ht : ∀ i, (tM : ZMod (e i).val) = (t (e i).val : ZMod (e i).val))
    (hlift : (Q.toList.prod : ℤ) ∣ tM + (primeTupleProduct P e : ℤ) * h₀) :
    |∑' n : ℤ, physicalWeight Q D ψ X n * ∏ i, orientedQuadraticValue ε t n (e i).val| ≤
      2 * Real.sqrt X * ‖originalPositiveFourier Q hQ D (primeTupleProduct P e) N h₀
        ((tM : ℝ) / primeTupleProduct P e) ((primeTupleProduct P e : ℝ) / X) (𝓕 ψ)‖ := by
  let : NeZero (primeTupleProduct P e) := ⟨(primeTupleProduct_pos P hP e).ne'⟩
  have hval : ((tM : ZMod (primeTupleProduct P e)).val : ℤ) = tM := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt htM htMlt]
  have hr : (((tM : ZMod (primeTupleProduct P e)).val : ℕ) : ℝ) = tM := by
    exact_mod_cast hval
  rw [physical_tuple_jacobi_norm Q P hP D ψ hreal X ε hε t e tM ht]
  have hh := amplified_jacobi_positive_bound Q hQ D (primeTupleProduct P e) N h₀ hcop
    (primeTupleProduct_squarefree P hP e) (primeTupleProduct_odd P hodd e)
    (primeTupleProduct_one_lt P hP hk e) (tM : ZMod (primeTupleProduct P e))
    (by simpa only [hval] using hlift) ψ hreal X H hX hH hcut hsupp
  simpa only [hval, hr] using hh

end Ostmann

end OAI
