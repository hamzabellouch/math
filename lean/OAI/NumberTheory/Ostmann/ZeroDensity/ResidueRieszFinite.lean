import OAI.NumberTheory.Ostmann.ZeroDensity.RieszCanonicalResidueMain
import OAI.NumberTheory.Ostmann.ZeroDensity.IntegratedThetaMain
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszFinite

namespace OAI

/-! # Exact real finite sums underlying the residue-class contour -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def residueMangoldtWeight (q a n : ℕ) : ℝ :=
  if (n : ZMod q) = (a : ZMod q) then ArithmeticFunction.vonMangoldt n else 0

noncomputable def residuePsi (q a : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, residueMangoldtWeight q a n

theorem residueMangoldtWeight_nonneg (q a n : ℕ) : 0 ≤ residueMangoldtWeight q a n := by
  unfold residueMangoldtWeight
  split_ifs <;> positivity

@[simp] theorem residueMangoldtWeight_zero (q a : ℕ) : residueMangoldtWeight q a 0 = 0 := by
  simp [residueMangoldtWeight]

theorem rieszResidueMean_eq_tsum (q a : ℕ) (X : ℝ) (hX : 0 < X) :
    rieszResidueMean q (a : ZMod q) X =
      ∑' n : ℕ, (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp
    · have hlarge : X < n := Nat.lt_of_floor_lt (by simp only [Finset.mem_Ioc] at hn; omega)
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hs]
  unfold rieszResidueMean rieszTwistMean
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : (n : ZMod q) = (a : ZMod q)
  · simp only [residueMangoldtWeight, hn, ite_true, mul_one]
  · simp only [residueMangoldtWeight, hn, ite_false, mul_zero, Complex.ofReal_zero, zero_mul]

theorem rieszResidueMean_finite (q a N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    (X : ℂ) * rieszResidueMean q (a : ZMod q) X =
      (finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X : ℝ) := by
  have hs (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
      (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) = 0 := by
    have hNn : N < n := by simpa using hn
    have hxn : X < n := hXN.trans_lt (by exact_mod_cast hNn)
    rw [rieszPrimeTest_scale X n hX, max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]
    simp
  rw [rieszResidueMean_eq_tsum q a X hX, tsum_eq_sum hs, Finset.mul_sum]
  unfold finiteRieszSum
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [rieszPrimeTest_scale X n hX]
  push_cast
  field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']

theorem rieszContourWeight_real (X β : ℝ) (hX : 0 < X) :
    rieszContourWeight X (β : ℂ) = (X ^ β / (β * (β + 1)) : ℝ) := by
  rw [rieszContourWeight, ← Complex.ofReal_cpow hX.le]
  unfold rieszMellinKernel
  push_cast
  ring

theorem riesz_residue_main_scale (φ χ β X : ℝ) (hX : 0 < X) :
    (X : ℂ) * ((φ : ℂ)⁻¹ * ((X / 2 : ℝ) - (χ : ℂ) * rieszContourWeight X (β : ℂ))) =
      (integratedThetaMain φ χ β X : ℝ) := by
  rw [rieszContourWeight_real X β hX]
  unfold integratedThetaMain
  rw [Real.rpow_add hX, Real.rpow_one]
  push_cast
  ring

theorem residueRieszMean_finite_error (q a N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    |finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X -
        integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
          (pageBeta (actualLocalZero q)) X| =
      X * ‖rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
        ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
          rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))‖ := by
  have he : ((finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X -
      integratedThetaMain q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) X : ℝ) : ℂ) =
      (X : ℂ) * (rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
        ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
          rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))) := by
    have hs := riesz_residue_main_scale (q.totient : ℝ)
      (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X hX
    simp only [Complex.ofReal_natCast] at hs
    rw [mul_sub, rieszResidueMean_finite q a N X hX hXN, hs, Complex.ofReal_sub]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]

theorem residue_finite_count (q a N : ℕ) (X : ℝ) (hX : 0 ≤ X) (hXN : X ≤ N) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X), residueMangoldtWeight q a n) =
      residuePsi q a X := by
  unfold residuePsi
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro hn
    exact ⟨Nat.zero_le _, (Nat.le_floor_iff hX).mpr hn.2⟩
  · intro hn
    have hnx := (Nat.le_floor_iff hX).mp hn.2
    have hnN : n ≤ N := by exact_mod_cast (hnx.trans hXN)
    exact ⟨by omega, hnx⟩

end Ostmann

end OAI
