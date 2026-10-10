import OAI.NumberTheory.DirichletL.Hecke.Euler

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, ite_eq_right hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, ite_eq_right hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, ite_eq_right hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI
