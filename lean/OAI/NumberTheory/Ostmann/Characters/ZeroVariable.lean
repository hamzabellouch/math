import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.ZeroVariable
open MvPolynomial

def setZero {ι:Type*} [DecidableEq ι] (i:ι) : MvPolynomial ι ℤ→+*MvPolynomial ι ℤ :=
  eval₂Hom C (fun j=>if j=i then 0 else X j)

theorem eval₂_setZero {ι R:Type*} [DecidableEq ι] [CommRing R]
    (i:ι) (P:MvPolynomial ι ℤ) (f:ℤ→+*R) (x:ι→R) (hi:x i=0) :
    eval₂ f x (setZero i P)=eval₂ f x P := by
  change eval₂ f x (eval₂ C (fun j=>if j=i then 0 else X j) P)=_
  rw [← eval₂_assoc]
  apply congrArg (fun y:ι→R=>eval₂ f y P)
  funext j
  by_cases hj:j=i
  · subst j
    simp only [ite_true,eval₂_zero,hi]
  · simp only [hj,ite_false,eval₂_X]

theorem prime_dvd_eval_of_setZero_eq_zero {ι:Type*} [DecidableEq ι]
    (i:ι) (P:MvPolynomial ι ℤ) (hP:setZero i P=0)
    (x:ι→ℤ) (p:ℕ) (hi:x i=(p:ℤ)) : (p:ℤ)∣eval x P := by
  have hz : (x i:ZMod p)=0 := by simp only [hi,Int.cast_natCast,ZMod.natCast_self]
  have he : eval₂ (Int.castRingHom (ZMod p)) (fun j=>(x j:ZMod p)) P=0 := by
    rw [← eval₂_setZero i P (Int.castRingHom (ZMod p)) (fun j=>(x j:ZMod p)) hz,hP]
    exact eval₂_zero _ _
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  change (Int.castRingHom (ZMod p)) (eval x P)=0
  rw [eval₂_comp]
  exact he

theorem prime_dvd_reconstructed_of_setZero_eq_zero {ι:Type*} [DecidableEq ι]
    (i:ι) (P:MvPolynomial ι ℤ) (hP:setZero i P=0)
    (x:ι→ℤ) (p:ℕ) (hi:x i=(p:ℤ)) (D y:ℤ)
    (hclear:D*y=eval x P) (hcop:IsCoprime (p:ℤ) D) : (p:ℤ)∣y := by
  apply hcop.dvd_of_dvd_mul_left
  rw [hclear]
  exact prime_dvd_eval_of_setZero_eq_zero i P hP x p hi

end Ostmann.Characters.ZeroVariable

end

end OAI
