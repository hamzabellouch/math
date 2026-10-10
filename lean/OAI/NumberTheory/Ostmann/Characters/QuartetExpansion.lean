import OAI.NumberTheory.Ostmann.Characters.QuartetParseval
import OAI.NumberTheory.Ostmann.Characters.UniformMellin

namespace OAI

/-!
# Exact Mellin expansion of the two-bad quartet term

The pair function is zero at a zero difference or ratio. The extra
multiplicative character also kills zero differences, so the full-field
convolution and the valid-pair formula agree exactly.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetExpansionFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def fieldBottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) : ℂ :=
  if hd : d = 0 then 0 else if ht : t = 0 then 0 else
    bottomPairValue g (Units.mk0 d hd) (Units.mk0 t ht)

theorem fieldBottomPairValue_expansion {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) (hd : d ≠ 0) :
    fieldBottomPairValue g d t =
      ∑ χ : MulChar (ZMod p) ℂ, pairAutocorrelation g χ d * χ t := by
  classical
  by_cases ht : t = 0
  · simp [fieldBottomPairValue, ht, MulChar.map_zero]
  · have h := mellin_inversion (bottomPairValue g (Units.mk0 d hd)) (Units.mk0 t ht)
    simp only [bottomPair_mellin_autocorrelation, Units.val_mk0] at h
    simpa only [fieldBottomPairValue, hd, ht, dite_false, pairAutocorrelation] using h.symm

noncomputable def twoBadQuartetValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p,
    fieldBottomPairValue g d ((z : ZMod p) / (d - y)) *
      fieldBottomPairValue h (d - y) ((t : ZMod p) / d) * ν (d / (d - y))

theorem twoBadQuartetValue_eq_synthesis {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) :
    twoBadQuartetValue g h ν y z t =
      quartetSynthesis (pairAutocorrelation g) (pairAutocorrelation h)
        (fun _ ψ => ν * ψ⁻¹) (fun χ _ => ν⁻¹ * χ⁻¹) y z t := by
  classical
  unfold twoBadQuartetValue quartetSynthesis additiveDifferenceConvolution
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (t := (Finset.univ : Finset (ZMod p)))]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · simp [hd, fieldBottomPairValue, MulChar.map_zero]
  by_cases he : d - y = 0
  · simp [he, fieldBottomPairValue, MulChar.map_zero]
  rw [fieldBottomPairValue_expansion g d _ hd,
    fieldBottomPairValue_expansion h (d - y) _ he]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  simp only [div_eq_mul_inv, map_mul, ← MulChar.inv_apply',
    MulChar.coeToFun_mul, Pi.mul_apply]
  ring

/-- The valid two-bad local average is exactly the Fourier expression already bounded. -/
theorem twoBadQuartetValue_parseval {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (ν : MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖twoBadQuartetValue g h ν y z t‖ ^ 2)) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (fun d => pairAutocorrelation g χ d * (ν * ψ⁻¹) d) a‖ ^ 2 *
          ‖additiveFourier (fun e => pairAutocorrelation h ψ e * (ν⁻¹ * χ⁻¹) e) (-a)‖ ^ 2 := by
  simp_rw [twoBadQuartetValue_eq_synthesis]
  exact quartetSynthesis_parseval _ _ _ _

end Ostmann

end OAI
