import Mathlib

namespace OAI

section
namespace ElementaryPositivity.IndependentCenters
variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def eval (z w : ℚ) : Polynomial (Polynomial A) →+* A :=
  (Polynomial.evalRingHom (algebraMap ℚ A z)).comp
    (Polynomial.evalRingHom (algebraMap ℚ (Polynomial A) w))

noncomputable def substitute (r : Polynomial (Polynomial A)) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) r) Polynomial.X

omit [Algebra ℚ A] in
@[simp] lemma substitute_C_C (r : Polynomial (Polynomial A)) (a : A) :
    substitute r (Polynomial.C (Polynomial.C a))=Polynomial.C (Polynomial.C a) := by
  simp [substitute]

omit [Algebra ℚ A] in
@[simp] lemma substitute_C_X (r : Polynomial (Polynomial A)) :
    substitute r (Polynomial.C Polynomial.X)=r := by
  simp [substitute]

omit [Algebra ℚ A] in
@[simp] lemma substitute_X (r : Polynomial (Polynomial A)) :
    substitute r Polynomial.X=Polynomial.X := by
  simp [substitute]

@[simp] lemma eval_C_C (z w : ℚ) (a : A) :
    eval z w (Polynomial.C (Polynomial.C a))=a := by
  change ((Polynomial.C (Polynomial.C a)).eval _).eval _=a
  rw [Polynomial.eval_C,Polynomial.eval_C]

@[simp] lemma eval_C_X (z w : ℚ) :
    eval (A:=A) z w (Polynomial.C Polynomial.X)=algebraMap ℚ A z := by
  change ((Polynomial.C Polynomial.X).eval _).eval _=_
  rw [Polynomial.eval_C,Polynomial.eval_X]

@[simp] lemma eval_X (z w : ℚ) :
    eval (A:=A) z w Polynomial.X=algebraMap ℚ A w := by
  change ((Polynomial.X : Polynomial (Polynomial A)).eval _).eval _=_
  rw [Polynomial.eval_X,Polynomial.algebraMap_apply,Polynomial.eval_C]

noncomputable def plus : Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  substitute (Polynomial.C Polynomial.X+Polynomial.X)
noncomputable def minus : Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  substitute (Polynomial.C Polynomial.X-Polynomial.X)

omit [Algebra ℚ A] in
lemma minus_plus : (minus (A:=A)).comp plus=RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply,minus,plus]
    · simp [RingHom.comp_apply,minus,plus]
  · simp [RingHom.comp_apply,minus,plus]

omit [Algebra ℚ A] in
lemma plus_minus : (plus (A:=A)).comp minus=RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply,minus,plus]
    · simp [RingHom.comp_apply,minus,plus]
  · simp [RingHom.comp_apply,minus,plus]

omit [Algebra ℚ A] in
@[simp] lemma minus_plus_apply (p : Polynomial (Polynomial A)) : minus (plus p)=p :=
  RingHom.congr_fun minus_plus p
omit [Algebra ℚ A] in
@[simp] lemma plus_minus_apply (p : Polynomial (Polynomial A)) : plus (minus p)=p :=
  RingHom.congr_fun plus_minus p

lemma eval_plus (z w : ℚ) (p : Polynomial (Polynomial A)) :
    eval z w (plus p)=eval (z+w) w p := by
  have h : (eval (A:=A) z w).comp plus=eval (z+w) w := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        simp [RingHom.comp_apply,plus]
      · simp [RingHom.comp_apply,plus]
    · simp [RingHom.comp_apply,plus]
  exact RingHom.congr_fun h p

omit [Algebra ℚ A] in
lemma diagonal_dvd_of_relative_dvd (p : Polynomial (Polynomial A)) (m : ℕ)
    (h : Polynomial.C (Polynomial.X^m) ∣ plus p) :
    (Polynomial.C Polynomial.X-Polynomial.X)^m ∣ p := by
  obtain ⟨q,hq⟩ := h
  refine ⟨minus q,?_⟩
  have hm := congrArg minus hq
  rw [minus_plus_apply,map_mul] at hm
  simpa only [map_pow,minus,substitute_C_X] using hm

noncomputable def diagonal : Polynomial (Polynomial A) :=
  Polynomial.X-Polynomial.C Polynomial.X

def DiagonalDivides (m : ℕ) (p : Polynomial (Polynomial A)) : Prop :=
  diagonal^m ∣ p

omit [Algebra ℚ A] in
lemma diagonalDivides_of_relative (p : Polynomial (Polynomial A)) (m : ℕ)
    (h : Polynomial.C (Polynomial.X^m) ∣ plus p) : DiagonalDivides m p := by
  let : CommRing (Polynomial A) := inferInstance
  let : CommRing (Polynomial (Polynomial A)) := inferInstance
  have hd:=diagonal_dvd_of_relative_dvd p m h
  have ha : diagonal (A:=A) ∣ Polynomial.C Polynomial.X-Polynomial.X := by
    refine ⟨-1,?_⟩
    simp only [diagonal,mul_neg,mul_one,neg_sub]
  exact (pow_dvd_pow_of_dvd ha m).trans hd

end ElementaryPositivity.IndependentCenters

end

end OAI
