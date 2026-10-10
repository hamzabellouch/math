import OAI.NumberTheory.JointDickman.Probability.FixedResidueReduction
import OAI.NumberTheory.JointDickman.Counting.DilatedWindowEnergy

namespace OAI

/-! # Dividing a residue class does not increase its normalized energy -/
namespace JointDickman
open Finset MeasureTheory Classical

theorem residueBinAverage_dilate_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    (w v : ArithmeticFunction ℝ) (c : ℝ)
    {d : ℕ} (hd : 0 < d) (e a : ℕ) (hc : 0 ≤ c ∧ c ≤ d)
    (hweight : ∀ k, w (d*k) = c*v k)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z‖^2) ≤
    (1/(X/d))*(∫ z in (X/d)..2*(X/d), ‖residueBinAverage E ζ μ v (a : ZMod e) (H/d) z‖^2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let C : ℝ := c/(d : ℝ)
  let f : ℝ → ℂ := residueBinAverage E ζ μ v (a : ZMod e) (H/d)
  have he z : residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z = (C : ℂ)*f (z/d) := by
    simpa only [C,f,Complex.ofReal_div,Complex.ofReal_natCast] using
      residueBinAverage_dilate E ζ μ w v c hd e a hweight hbin hH z
  simp_rw [he]
  rw [normalized_dilate_energy f C hdR hX]
  have hC0 : 0 ≤ C := div_nonneg hc.1 hdR.le
  have hC1 : C ≤ 1 := (div_le_one hdR).mpr hc.2
  have hC2 : C^2 ≤ 1 := by nlinarith
  apply mul_le_of_le_one_left _ hC2
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg
    (by have hh := div_pos hX hdR; linarith : X/(d : ℝ) ≤ 2*(X/d)) (fun _ _ => sq_nonneg _)

theorem residueBinAverage_fixed_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℕ → ℝ)
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    {d : ℕ} (hd : 0 < d) (e a : ℕ)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X,
      ‖residueBinAverage E ζ μ (finitePrimeWeight P t) ((d*a : ℕ) : ZMod (d*e)) H z‖^2) ≤
    (1/(X/d))*(∫ z in (X/d)..2*(X/d),
      ‖residueBinAverage E ζ μ (finitePrimeWeight P (fun p => if p ∣ d then 1 else t p))
        (a : ZMod e) (H/d) z‖^2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let c : ℝ := finitePrimeWeight P t d/(d : ℝ)
  let f : ℝ → ℂ := residueBinAverage E ζ μ
    (finitePrimeWeight P (fun p => if p ∣ d then 1 else t p)) (a : ZMod e) (H/d)
  have he z : residueBinAverage E ζ μ (finitePrimeWeight P t)
      ((d*a : ℕ) : ZMod (d*e)) H z = (c : ℂ)*f (z/d) := by
    simpa only [c,f,Complex.ofReal_div,Complex.ofReal_natCast] using
      residueBinAverage_fixed_divisor E ζ μ hP t hd e a hbin hH z
  simp_rw [he]
  rw [normalized_dilate_energy f c hdR hX]
  have hb := finitePrimeWeight_bounds ht d
  have hc0 : 0 ≤ c := div_nonneg hb.1 hdR.le
  have hc1 : c ≤ 1 := (div_le_one hdR).mpr (hb.2.trans (by exact_mod_cast hd))
  have hc2 : c^2 ≤ 1 := by nlinarith
  apply mul_le_of_le_one_left _ hc2
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg (by have hh := div_pos hX hdR; linarith : X/(d : ℝ) ≤ 2*(X/d)) (fun _ _ => sq_nonneg _)

end JointDickman

end OAI
