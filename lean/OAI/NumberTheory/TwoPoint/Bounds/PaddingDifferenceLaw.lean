import OAI.NumberTheory.TwoPoint.Bounds.PaddingCharacteristic
import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Analysis.Complex.Trigonometric

namespace OAI

/-! The actual independent three-point padding difference law and its
characteristic product. At each prime the two nonzero atoms have the
manuscript's exact probability `4/(5(p+4))`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingDifferenceAtom (p : ℕ) (e : Fin 3) : ℝ :=
  if e = 0 then 1 - 8 / (5 * ((p : ℝ) + 4)) else 4 / (5 * ((p : ℝ) + 4))

noncomputable def paddingDifferenceStep (p : ℕ) (e : Fin 3) : ℝ :=
  if e = 0 then 0 else if e = 1 then Real.log p else -Real.log p

noncomputable def paddingStepLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw (Fin 3) where
  weight := paddingDifferenceAtom p
  nonneg e := by
    have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hd : 0 < 5 * ((p : ℝ) + 4) := by positivity
    unfold paddingDifferenceAtom
    split_ifs
    · have hh : 8 / (5 * ((p : ℝ) + 4)) ≤ 1 := (div_le_one hd).mpr (by linarith)
      linarith
    · positivity
  total := by
    rw [Fin.sum_univ_three]
    norm_num [paddingDifferenceAtom]
    ring

noncomputable def paddingDifferenceLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Fin 3) :=
  FiniteLaw.independent (fun p : Q => paddingStepLaw p (hQ p p.property))

noncomputable def paddingDifferenceValue (Q : Finset ℕ) (x : Q → Fin 3) : ℝ :=
  ∑ p : Q, paddingDifferenceStep p (x p)

lemma paddingStep_characteristic (p : ℕ) (t : ℝ) :
    (∑ e : Fin 3, (paddingDifferenceAtom p e : ℂ) *
      Complex.exp (((t * paddingDifferenceStep p e : ℝ) : ℂ) * Complex.I)) =
      (paddingCharacteristicFactor p t : ℂ) := by
  rw [Fin.sum_univ_three]
  norm_num only [paddingDifferenceAtom, paddingDifferenceStep, Fin.isValue,
    Fin.zero_eta, ↓reduceIte, Fin.reduceEq, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one]
  rw [show t * -Real.log p = -(t * Real.log p) by ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  unfold paddingCharacteristicFactor
  push_cast
  ring

/-- The complete finite-law characteristic function is the real,
nonnegative product estimated in `PaddingCharacteristic`. -/
theorem paddingDifference_characteristic (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    (∑ x : Q → Fin 3, ((paddingDifferenceLaw Q hQ).weight x : ℂ) *
      Complex.exp (((t * paddingDifferenceValue Q x : ℝ) : ℂ) * Complex.I)) =
        (paddingCharacteristic Q t : ℂ) := by
  have hexp (x : Q → Fin 3) :
      Complex.exp (((t * paddingDifferenceValue Q x : ℝ) : ℂ) * Complex.I) =
        ∏ p : Q, Complex.exp (((t * paddingDifferenceStep p (x p) : ℝ) : ℂ) * Complex.I) := by
    unfold paddingDifferenceValue
    rw [mul_sum, Complex.ofReal_sum, sum_mul, Complex.exp_sum]
  simp only [paddingDifferenceLaw, FiniteLaw.independent, paddingStepLaw,
    Complex.ofReal_prod, hexp, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (p : Q) (e : Fin 3) =>
    (paddingDifferenceAtom p e : ℂ) *
      Complex.exp (((t * paddingDifferenceStep p e : ℝ) : ℂ) * Complex.I))]
  simp only [paddingStep_characteristic]
  unfold paddingCharacteristic
  rw [Complex.ofReal_prod]
  exact (prod_subtype (p := fun p : ℕ => p ∈ Q) Q (fun _ => Iff.rfl)
    (fun p => (paddingCharacteristicFactor p t : ℂ))).symm

lemma paddingDifference_cosine (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (t : ℝ) :
    (paddingDifferenceLaw Q hQ).average (fun x => Real.cos (t * paddingDifferenceValue Q x)) =
      paddingCharacteristic Q t := by
  have hh := congrArg Complex.re (paddingDifference_characteristic Q hQ t)
  simpa [FiniteLaw.average, Complex.mul_re, Complex.exp_re] using hh

end TwoPointCorrelations

end OAI
