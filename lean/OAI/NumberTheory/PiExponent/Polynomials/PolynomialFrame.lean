import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree

namespace OAI

namespace PiExponentApprox

noncomputable section

abbrev FramePolynomial (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

def logarithmicDerivation (m : ℕ) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  (MvPolynomial.X (0 : Fin (m + 1)) : FramePolynomial m) •
    MvPolynomial.pderiv (R := ℂ) (0 : Fin (m + 1)) +
    ∑ i : Fin m, MvPolynomial.pderiv (R := ℂ) i.succ

def polynomialFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  if i = 0 then logarithmicDerivation m else MvPolynomial.pderiv i

theorem derivation_finset_sum_apply {α : Type*} (m : ℕ) (s : Finset α)
    (D : α → Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (p : FramePolynomial m) : (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (m : ℕ) (p : FramePolynomial m) :
    logarithmicDerivation m p =
      MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ p := by
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem polynomialFrame_zero (m : ℕ) :
    polynomialFrame m 0 = logarithmicDerivation m := by
  simp only [polynomialFrame, ite_true]

@[simp] theorem polynomialFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0) :
    polynomialFrame m i = MvPolynomial.pderiv i := by
  simp only [polynomialFrame, ite_eq_right hi]

theorem polynomial_pderiv_commute (m : ℕ) (i j : Fin (m + 1))
    (p : FramePolynomial m) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  by_cases hij : i = j
  · subst j
    rfl
  · apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply,
      Finsupp.single_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij),
      add_zero]
    rw [show d + Finsupp.single i 1 + Finsupp.single j 1 =
      d + Finsupp.single j 1 + Finsupp.single i 1 by ac_rfl]
    ring

theorem pderiv_logarithmicDerivation_commute (m : ℕ) (i : Fin (m + 1))
    (hi : i ≠ 0) (p : FramePolynomial m) :
    MvPolynomial.pderiv i (logarithmicDerivation m p) =
      logarithmicDerivation m (MvPolynomial.pderiv i p) := by
  have hEuler :
      MvPolynomial.pderiv i
        (MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p) =
      MvPolynomial.X (0 : Fin (m + 1)) *
        MvPolynomial.pderiv 0 (MvPolynomial.pderiv i p) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (Ne.symm hi),
      zero_mul, zero_add, polynomial_pderiv_commute m i 0 p]
  have hSum : MvPolynomial.pderiv i (∑ j : Fin m, MvPolynomial.pderiv j.succ p) =
      ∑ j : Fin m, MvPolynomial.pderiv j.succ (MvPolynomial.pderiv i p) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact polynomial_pderiv_commute m i j.succ p
  rw [logarithmicDerivation_apply, map_add, hEuler, hSum]
  exact (logarithmicDerivation_apply m (MvPolynomial.pderiv i p)).symm

theorem polynomialFrame_commute (m : ℕ) (i j : Fin (m + 1))
    (p : FramePolynomial m) :
    polynomialFrame m i (polynomialFrame m j p) =
      polynomialFrame m j (polynomialFrame m i p) := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rfl
    · rw [polynomialFrame_zero, polynomialFrame_pos m j hj]
      exact (pderiv_logarithmicDerivation_commute m j hj p).symm
  · by_cases hj : j = 0
    · subst j
      rw [polynomialFrame_zero, polynomialFrame_pos m i hi]
      exact pderiv_logarithmicDerivation_commute m i hi p
    · rw [polynomialFrame_pos m i hi, polynomialFrame_pos m j hj]
      exact polynomial_pderiv_commute m i j p

@[simp] theorem polynomialFrame_add (m : ℕ) (i : Fin (m + 1))
    (p q : FramePolynomial m) :
    polynomialFrame m i (p + q) = polynomialFrame m i p + polynomialFrame m i q :=
  map_add _ _ _

theorem polynomialFrame_mul (m : ℕ) (i : Fin (m + 1))
    (p q : FramePolynomial m) :
    polynomialFrame m i (p * q) =
      polynomialFrame m i p * q + p * polynomialFrame m i q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

@[simp] theorem polynomialFrame_C (m : ℕ) (i : Fin (m + 1)) (a : ℂ) :
    polynomialFrame m i (MvPolynomial.C a) = 0 := by
  rw [MvPolynomial.C_eq_algebraMap]
  exact Derivation.map_algebraMap _ a

theorem HasWeightedDegreeLE.logarithmicDerivation {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) :
    HasWeightedDegreeLE w N (PiExponentApprox.logarithmicDerivation m p) := by
  rw [logarithmicDerivation_apply]
  apply (hp.X_mul_pderiv 0).add
  exact HasWeightedDegreeLE.sum Finset.univ _
    (fun i _ => hp.pderiv_preserves i.succ (hw i.succ))

theorem HasWeightedDegreeLE.polynomialFrame {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 1)) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrame m i p) := by
  by_cases hi : i = 0
  · subst i
    rw [polynomialFrame_zero]
    exact hp.logarithmicDerivation hw
  · rw [polynomialFrame_pos m i hi]
    exact hp.pderiv_preserves i (hw i)

def polynomialFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (p : FramePolynomial m) : FramePolynomial m :=
  word.foldr (fun i q => polynomialFrame m i q) p

@[simp] theorem polynomialFrameWord_nil (m : ℕ) (p : FramePolynomial m) :
    polynomialFrameWord m [] p = p := rfl

@[simp] theorem polynomialFrameWord_cons (m : ℕ) (i : Fin (m + 1))
    (word : List (Fin (m + 1))) (p : FramePolynomial m) :
    polynomialFrameWord m (i :: word) p =
      polynomialFrame m i (polynomialFrameWord m word p) := rfl

theorem polynomialFrame_commute_word (m : ℕ) (i : Fin (m + 1))
    (word : List (Fin (m + 1))) (p : FramePolynomial m) :
    polynomialFrame m i (polynomialFrameWord m word p) =
      polynomialFrameWord m word (polynomialFrame m i p) := by
  induction word with
  | nil => rfl
  | cons j word ih =>
      rw [polynomialFrameWord_cons, polynomialFrameWord_cons,
        polynomialFrame_commute m i j, ih]

theorem HasWeightedDegreeLE.polynomialFrameWord {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i)
    (word : List (Fin (m + 1))) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrameWord m word p) := by
  induction word with
  | nil => exact hp
  | cons i word ih => exact ih.polynomialFrame hw i

end
end PiExponentApprox

end OAI
