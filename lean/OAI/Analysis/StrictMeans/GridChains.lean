import OAI.Analysis.StrictMeans.PlaneRectangle

namespace OAI

section
open Polynomial
namespace StrictInverseFirstPower.Grid
noncomputable section

abbrev Chain := Polynomial (Polynomial ℚ)

def x : Chain := C X
def y : Chain := X

lemma x_sub_one_ne_zero : x - 1 ≠ 0 := by
  intro h
  have he := congrArg (fun p : Chain => (p.coeff 0).coeff 1) h
  norm_num [x,coeff_one] at he

lemma y_sub_one_ne_zero : y - 1 ≠ 0 := by
  intro h
  have he := congrArg (fun p : Chain => (p.coeff 1).coeff 0) h
  norm_num [y,coeff_one] at he

def boundary₁ (h v d : Chain) : Chain := (x-1)*h + (y-1)*v + (x*y-1)*d

def faceH (a b : Chain) : Chain := a-y*b
def faceV (a b : Chain) : Chain := x*a-b
def faceD (a b : Chain) : Chain := b-a

lemma boundary_face (a b : Chain) : boundary₁ (faceH a b) (faceV a b) (faceD a b) = 0 := by
  unfold boundary₁ faceH faceV faceD
  ring

lemma square_cycle_fills {h v : Chain} (hc : (x-1)*h+(y-1)*v=0) :
    ∃ s : Chain, h=(1-y)*s ∧ v=(x-1)*s := by
  have hv : eval (1 : Polynomial ℚ) h = 0 := by
    have he := congrArg (eval (1 : Polynomial ℚ)) hc
    simp only [eval_add,eval_mul,eval_sub,eval_one,eval_zero,x,y,eval_C,eval_X,
      sub_self,zero_mul,add_zero] at he
    have hn : (X : Polynomial ℚ)-1 ≠ 0 := by
      intro hn
      have ha := congrArg (fun p : Polynomial ℚ => p.coeff 1) hn
      norm_num [coeff_one] at ha
    exact (mul_eq_zero.mp he).resolve_left hn
  have hd : (y-1) ∣ h := by
    simpa only [y,C_1] using (dvd_iff_isRoot.mpr hv : (X-C (1 : Polynomial ℚ)) ∣ h)
  obtain ⟨a,ha⟩ := hd
  refine ⟨-a,?_,?_⟩
  · rw [ha]
    ring
  · have he : (y-1)*((x-1)*a+v)=0 := by
      rw [ha] at hc
      convert hc using 1
      ring
    have he' := (mul_eq_zero.mp he).resolve_left y_sub_one_ne_zero
    have hv' : v = -(x-1)*a := by linear_combination he'
    rw [hv']
    ring

lemma cycle_fills {h v d : Chain} (hc : boundary₁ h v d = 0) :
    ∃ a b : Chain, faceH a b = h ∧ faceV a b = v ∧ faceD a b = d := by
  have hs : (x-1)*(h+d)+(y-1)*(v+x*d)=0 := by
    unfold boundary₁ at hc
    convert hc using 1
    ring
  obtain ⟨s,hh,hv⟩ := square_cycle_fills hs
  refine ⟨s-d,s,?_,?_,?_⟩
  · unfold faceH
    linear_combination -hh
  · unfold faceV
    linear_combination -hv
  · unfold faceD
    ring

lemma face_eq_aux {R : Type*} [CommRing R] (Y : R) {a b c d : R}
    (hH : a-Y*b=c-Y*d) (hD : b-a=d-c) : (Y-1)*(b-d)=0 := by
  linear_combination -hH-hD

lemma face_boundary_injective : Function.Injective
    (fun p : Chain × Chain => (faceH p.1 p.2,faceV p.1 p.2,faceD p.1 p.2)) := by
  intro p q he
  have hH := congrArg (fun a : Chain × Chain × Chain => a.1) he
  have hD := congrArg (fun a : Chain × Chain × Chain => a.2.2) he
  change p.1-y*p.2 = q.1-y*q.2 at hH
  change p.2-p.1 = q.2-q.1 at hD
  have hm := face_eq_aux y hH hD
  have hp := (mul_eq_zero.mp hm).resolve_left y_sub_one_ne_zero
  have hb : p.2=q.2 := sub_eq_zero.mp hp
  have ha : p.1=q.1 := by
    rw [hb] at hH
    exact sub_left_injective hH
  exact Prod.ext ha hb

end
end StrictInverseFirstPower.Grid

end

end OAI
