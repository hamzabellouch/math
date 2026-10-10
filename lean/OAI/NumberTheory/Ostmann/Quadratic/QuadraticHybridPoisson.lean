import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyCutoff
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeMain

namespace OAI

/-! # Exact passage between the physical and Fourier lattice tails -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticLatticeTail (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else ψ ((n : ℝ) * Y)

noncomputable def quadraticLatticeWindow (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(L : ℤ)) L, if n = 0 then 0 else ψ ((n : ℝ) * Y)

noncomputable def quadraticLatticeOuter (ψ : 𝓢(ℝ, ℂ)) (Y : ℝ) (L : ℕ) : ℂ :=
  ∑' n : ℤ, if L < n.natAbs then ψ ((n : ℝ) * Y) else 0

 theorem quadraticLatticeTail_window (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y) (L : ℕ) :
    quadraticLatticeTail ψ Y = quadraticLatticeWindow ψ Y L + quadraticLatticeOuter ψ Y L :=
  quadratic_frequency_window ψ hY L

 theorem quadraticLatticeTail_poisson (ψ : 𝓢(ℝ, ℂ)) {X d : ℝ}
    (hX : 0 < X) (hd : 0 < d) :
    ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d) =
      ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0 := by
  have hsplit (f : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
      (∑' n : ℤ, f ((n : ℝ) * Y)) = f 0 + quadraticLatticeTail f Y := by
    have hs : Summable (fun n : ℤ => f ((n : ℝ) * Y)) := by
      apply Summable.of_norm
      simpa only [div_inv_eq_mul] using quadratic_scaled_summable f (inv_pos.mpr hY)
    simpa only [Int.cast_zero, zero_mul, quadraticLatticeTail] using hs.tsum_eq_add_tsum_ite 0
  have hp := quadratic_scaled_poisson ψ (div_pos hX hd)
  simp only [div_div_eq_mul_div, mul_div_assoc] at hp
  have hp' : (∑' n : ℤ, ψ ((n : ℝ) * (d / X))) =
      ((X / d : ℝ) : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * (X / d)) := by
    simpa only [mul_div_assoc] using hp
  rw [hsplit ψ (d / X) (div_pos hd hX), hsplit (𝓕 ψ) (X / d) (div_pos hX hd)] at hp'
  linear_combination -hp'

 theorem quadraticCoprimeRemainder_tail {q : ℕ} (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) :
    quadraticCoprimeRemainder q ψ X =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeTail (𝓕 ψ) (X / d) := by
  unfold quadraticCoprimeRemainder quadraticLatticeTail
  simp only [mul_div_assoc]

 theorem quadraticCoprimeRemainder_hybrid {q : ℕ} (ψ : 𝓢(ℝ, ℂ))
    {X U V : ℝ} (hX : 0 < X) (_hUV : U ≤ V) (L : ℕ) :
    quadraticCoprimeRemainder q ψ X =
      ∑ d ∈ q.divisors,
        if (d : ℝ) ≤ U then
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)
        else if (d : ℝ) ≤ V then
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
            (quadraticLatticeWindow (𝓕 ψ) (X / d) L + quadraticLatticeOuter (𝓕 ψ) (X / d) L)
        else (ArithmeticFunction.moebius d : ℂ) *
          (ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0) := by
  rw [quadraticCoprimeRemainder_tail]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  by_cases hdu : (d : ℝ) ≤ U
  · rw [ite_eq_left hdu]
  · rw [ite_eq_right hdu]
    by_cases hdv : (d : ℝ) ≤ V
    · rw [ite_eq_left hdv, quadraticLatticeTail_window (𝓕 ψ) (div_pos hX hdR) L]
    · rw [ite_eq_right hdv, mul_assoc, quadraticLatticeTail_poisson ψ hX hdR]

end Ostmann

end OAI
