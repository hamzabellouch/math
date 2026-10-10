import OAI.NumberTheory.Ostmann.Characters.MixedFourier

namespace OAI

/-!
# Unit changes of the bottom-pair difference

Multiplying the difference by a unit is equivalent to composing the test
with that multiplication. Thus the uniform Mellin estimate applies to
both difference orientations with its original constant.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance orientedFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem additiveAutocorrelation_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (d : ZMod p) :
    additiveAutocorrelation (fun x => c * f x) d =
      (‖c‖ ^ 2 : ℝ) * additiveAutocorrelation f d := by
  simp only [additiveAutocorrelation, map_mul]
  calc
    _ = (c * conj c) * ((p : ℂ)⁻¹ * ∑ x : ZMod p, f x * conj (f (x - d))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Complex.mul_conj']; push_cast; ring

theorem additiveAutocorrelation_unit_mul {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (d : ZMod p) :
    additiveAutocorrelation (fun x => f ((u : ZMod p) * x)) d =
      additiveAutocorrelation f ((u : ZMod p) * d) := by
  unfold additiveAutocorrelation
  congr 1
  calc
    _ = ∑ x : ZMod p, f ((u : ZMod p) * x) *
        conj (f ((u : ZMod p) * x - (u : ZMod p) * d)) := by
      simp only [mul_sub]
    _ = _ := (Equiv.mulLeft₀ (u : ZMod p) (Units.ne_zero u)).bijective.sum_comp
      (fun x => f x * conj (f (x - (u : ZMod p) * d)))

theorem characterTwist_unit_mul {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) (x : ZMod p) :
    characterTwist (fun y => g ((u : ZMod p) * y)) χ x =
      χ u * characterTwist g χ ((u : ZMod p) * x) := by
  have hc : χ u * conj (χ u) = 1 := by
    rw [Complex.mul_conj', norm_mulChar_unit χ u]
    norm_num
  simp only [characterTwist, map_mul]
  calc
    _ = (χ u * conj (χ u)) * (g ((u : ZMod p) * x) * conj (χ x)) := by rw [hc, one_mul]
    _ = _ := by ring

theorem pairAutocorrelation_unit_mul {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) (d : ZMod p) :
    pairAutocorrelation (fun y => g ((u : ZMod p) * y)) χ d =
      pairAutocorrelation g χ ((u : ZMod p) * d) := by
  have hfun : characterTwist (fun y => g ((u : ZMod p) * y)) χ =
      (fun x => χ u * characterTwist g χ ((u : ZMod p) * x)) :=
    funext (characterTwist_unit_mul g χ u)
  unfold pairAutocorrelation
  rw [hfun, additiveAutocorrelation_const_mul, norm_mulChar_unit χ u]
  simp only [one_pow, Complex.ofReal_one, one_mul, additiveAutocorrelation_unit_mul]

/-- The uniform estimate for either sign of the bottom-pair difference. -/
theorem uniform_mellin_bound_scaled {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : MixedFourierBound g ε)
    (u : (ZMod p)ˣ) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun d => pairAutocorrelation g χ ((u : ZMod p) * d) * χ d * η d) a‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  have hzero : g ((u : ZMod p) * 0) = 0 := by simpa only [mul_zero] using hg
  have hen : (∑ x : ZMod p, ‖g ((u : ZMod p) * x)‖ ^ 2) ≤ (p : ℝ) := by
    rw [unit_mul_energy]
    exact henergy
  simpa only [pairAutocorrelation_unit_mul] using
    uniform_mellin_bound_of_fourier_bound (fun x => g ((u : ZMod p) * x)) hzero hen ε
      (hε.unit_mul u) η a

end Ostmann

end OAI
