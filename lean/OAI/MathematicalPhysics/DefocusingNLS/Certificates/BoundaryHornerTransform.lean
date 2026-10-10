import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateSemantics

namespace OAI

/-! # Sound homogeneous Horner transforms for the three certificate charts -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

noncomputable def chartNumerator (U V : ℤ) : Polynomial ℂ := C (U : ℂ) + X * C (V : ℂ)
noncomputable def chartDenominator (J : ℤ) : Polynomial ℂ := 1 + X * C (J : ℂ)

noncomputable def polynomialTransformAux (U V J : ℤ) : List ℂ →
    Polynomial ℂ × Polynomial ℂ → Polynomial ℂ × Polynomial ℂ
  | [], qm => qm
  | a :: as, qm => polynomialTransformAux U V J as
      (qm.1 * chartNumerator U V + qm.2 * C a, qm.2 * chartDenominator J)

noncomputable def homogeneousHorner (U V J : ℤ) : List ℂ → Polynomial ℂ
  | [] => 0
  | a :: as => C a * chartDenominator J ^ as.length + chartNumerator U V * homogeneousHorner U V J as

theorem chartNumerator_sound (U V : ℤ) :
    EnclosesPolynomial [coefficient U 0 0, coefficient V 0 0] (chartNumerator U V) := by
  refine ⟨(U : ℂ), C (V : ℂ), ?_, ?_, rfl⟩
  · simpa [constant] using coefficient_sound (constant_sound U) 0
  · exact constant_sound V

theorem chartDenominator_sound (J : ℤ) :
    EnclosesPolynomial [coefficient 1 0 0, coefficient J 0 0] (chartDenominator J) := by
  simpa [chartDenominator, chartNumerator] using chartNumerator_sound 1 J

theorem polynomialTransformAux_append (U V J : ℤ) (as bs : List ℂ)
    (qm : Polynomial ℂ × Polynomial ℂ) :
    polynomialTransformAux U V J (as ++ bs) qm =
      polynomialTransformAux U V J bs (polynomialTransformAux U V J as qm) := by
  induction as generalizing qm with
  | nil => rfl
  | cons a as ih => exact ih _

theorem polynomialTransformAux_second (U V J : ℤ) (as : List ℂ)
    (qm : Polynomial ℂ × Polynomial ℂ) :
    (polynomialTransformAux U V J as qm).2 = qm.2 * chartDenominator J ^ as.length := by
  induction as generalizing qm with
  | nil => simp [polynomialTransformAux]
  | cons a as ih =>
    rw [polynomialTransformAux, ih]
    simp only [List.length_cons, pow_succ]
    ring

theorem polynomialTransformAux_reverse (U V J : ℤ) (as : List ℂ) :
    (polynomialTransformAux U V J as.reverse (0, 1)).1 = homogeneousHorner U V J as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons, polynomialTransformAux_append]
    simp only [polynomialTransformAux]
    rw [ih, polynomialTransformAux_second]
    simp only [one_mul, List.length_reverse, homogeneousHorner]
    ring

theorem transformAux_sound (U V J : ℤ) {as : List GaussianEnclosure} {zs : List ℂ}
    (has : List.Forall₂ (fun a z => a.Encloses z) as zs)
    {q m : EnclosurePolynomial} {Q M : Polynomial ℂ}
    (hq : EnclosesPolynomial q Q) (hm : EnclosesPolynomial m M) :
    EnclosesPolynomial (transformAux U V J as (q, m)).1
      (polynomialTransformAux U V J zs (Q, M)).1 ∧
    EnclosesPolynomial (transformAux U V J as (q, m)).2
      (polynomialTransformAux U V J zs (Q, M)).2 := by
  induction has generalizing q m Q M with
  | nil => exact ⟨hq, hm⟩
  | @cons a z as zs hz htail ih =>
    apply ih
    · exact addPolynomial_sound (mulPolynomial_sound hq (chartNumerator_sound U V))
        (mulPolynomial_sound hm ⟨z, 0, hz, rfl, by simp⟩)
    · exact mulPolynomial_sound hm (chartDenominator_sound J)

end DefocusingNLS.BoundaryCertificate

end OAI
