import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteStringReordering

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

def inputShift (d : I → ℕ) : ℤ := ∑ i,(d i:ℤ)*(κ i+1-a i i)
omit [DecidableEq I] in
@[simp] lemma inputShift_zero : inputShift a κ (0 : I → ℕ)=0 := by simp [inputShift]
omit [DecidableEq I] in
lemma inputShift_add (d e : I → ℕ) : inputShift a κ (d+e)=inputShift a κ d+inputShift a κ e := by
  simp [inputShift,add_mul,Finset.sum_add_distrib]

def normalizedEnergy (d : I → ℕ) (k : ℤ) : ℤ := inputShift a κ d-eulerForm a d d-2*k

omit [DecidableEq I] in
lemma normalizedEnergy_product (d e : I → ℕ) (k m : ℤ) :
    normalizedEnergy a κ (d+e) (k+m-eulerForm a d e)=
      normalizedEnergy a κ d k+normalizedEnergy a κ e m+(eulerForm a d e-eulerForm a e d) := by
  simp only [normalizedEnergy,inputShift_add,eulerForm_add_left,eulerForm_add_right]
  ring

variable (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def stringStartParameter (i : GlobalStringIndex a c η hc θ) : ℤ :=
  normalizedEnergy a κ i.1.val.1.val
    (stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2.2)

lemma stringLetterEnergy (i : GlobalStringIndex a c η hc θ) :
    normalizedEnergy a κ i.1.val.1.val (globalStringPolynomialDegree a c η hc θ i)=
      stringStartParameter a κ c η hc θ i-2*i.2.1 := by
  simp only [stringStartParameter,normalizedEnergy,globalStringPolynomialDegree]
  ring

lemma stringStartParity (i : GlobalStringIndex a c η hc θ) :
    globalColorSign a c η hc θ i.1.val i.1.val=1 ↔ Even (eulerForm a i.1.val.1.val i.1.val.1.val) := by
  by_cases he : Even (eulerForm a i.1.val.1.val i.1.val.1.val)
  · simp [globalColorSign,neg_one_zpow_eq_ite,he]
  · norm_num [globalColorSign,neg_one_zpow_eq_ite,he]

omit [DecidableEq I] hχ in
lemma inputShift_word {J : Type*} (w : J → SlopeWeight c η hc θ) (l : List J) :
    inputShift a κ (wordWeight c η hc θ w l).1.val=(l.map (fun i=>inputShift a κ (w i).1.val)).sum := by
  induction l with
  | nil => simp [wordWeight]
  | cons i l ih =>
    change inputShift a κ ((w i).1.val+(wordWeight c η hc θ w l).1.val)=_
    rw [inputShift_add,ih]
    rfl

lemma stringWordEnergy (l : StringPBWIndex a c η hc θ) :
    normalizedEnergy a κ (stringPBWGrade a c η hc θ l).1.1.val
      (stringPBWGrade a c η hc θ l).2=
      (l.val.map (fun i=>stringStartParameter a κ c η hc θ i-2*i.2.1)).sum := by
  have H:=wordPolynomialDegree_shift a c η hc θ
    (fun i : GlobalStringIndex a c η hc θ=>i.1.val) (globalStringPolynomialDegree a c η hc θ) l.val
  change inputShift a κ (wordWeight c η hc θ _ l.val).1.val-
    eulerForm a (wordWeight c η hc θ _ l.val).1.val (wordWeight c η hc θ _ l.val).1.val-
    2*wordPolynomialDegree a c η hc θ _ (globalStringPolynomialDegree a c η hc θ) l.val=_
  rw [sub_sub,add_comm (eulerForm a _ _),H,inputShift_word]
  have E : ∀ j : List (GlobalStringIndex a c η hc θ),
      (j.map (fun i=>inputShift a κ i.1.val.1.val)).sum -
        (j.map (fun i=>2*globalStringPolynomialDegree a c η hc θ i+
          eulerForm a i.1.val.1.val i.1.val.1.val)).sum =
        (j.map (fun i=>stringStartParameter a κ c η hc θ i-2*i.2.1)).sum := by
    intro j
    induction j with
    | nil => simp
    | cons i j ih =>
      simp only [List.map_cons,List.sum_cons]
      have H := stringLetterEnergy a κ c η hc θ i
      dsimp only [normalizedEnergy] at H
      linear_combination ih + H
  exact E l.val

noncomputable def stringSelectionEquiv :
    StringPBWIndex a c η hc θ ≃
      ElementaryPositivity.SignedSelection (fun i : GlobalStringIndex a c η hc θ=>
        globalColorSign a c η hc θ i.1.val i.1.val=1) :=
  ElementaryPositivity.signedWordSelectionEquiv _
end ElementaryPositivity.RawShuffle

end

end OAI
