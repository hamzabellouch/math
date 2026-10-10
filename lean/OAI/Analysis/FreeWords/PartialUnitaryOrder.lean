import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryAlgebra

namespace OAI

noncomputable section

namespace KKLocalPatching.PartialUnitary

variable {A : Type*} [Ring A] [StarRing A]

@[ext] theorem ext {v w : PartialUnitary A} (h : ∀ k, v.power k=w.power k) : v=w := by
  cases v; cases w
  simp_all only [mk.injEq,funext_iff]
  intro; trivial

def Extends (v w : PartialUnitary A) : Prop :=
  ∀ k, w.power k*v.support=v.power k ∧ v.support*w.power k=v.power k

instance : PartialOrder (PartialUnitary A) where
  le := Extends
  le_refl v k := ⟨v.mul_support k,v.support_mul k⟩
  le_trans v w z hvw hwz k := by
    constructor
    · calc
        _ = z.power k*(w.support*v.support) := by rw [show w.support*v.support=v.support from (hvw 0).1]
        _ = (z.power k*w.support)*v.support := by rw [mul_assoc]
        _ = _ := by rw [(hwz k).1,(hvw k).1]
    · calc
        _ = (v.support*w.support)*z.power k := by rw [show v.support*w.support=v.support from (hvw 0).2]
        _ = v.support*(w.support*z.power k) := by rw [mul_assoc]
        _ = _ := by rw [(hwz k).2,(hvw k).2]
  le_antisymm v w hvw hwv := by
    have hs : v.support=w.support := (hvw 0).1.symm.trans (hwv 0).2
    ext k
    rw [← (hvw k).1,hs,w.mul_support]

theorem cross_power {v w : PartialUnitary A} (h : v≤w) (k l : ℤ) :
    w.power k*v.power l=v.power (k+l) := by
  calc
    _ = w.power k*(v.support*v.power l) := by rw [v.support_mul]
    _ = (w.power k*v.support)*v.power l := by rw [mul_assoc]
    _ = _ := by rw [(h k).1,← v.add]

theorem cross_power' {v w : PartialUnitary A} (h : v≤w) (k l : ℤ) :
    v.power k*w.power l=v.power (k+l) := by
  calc
    _ = (v.power k*v.support)*w.power l := by rw [v.mul_support]
    _ = v.power k*(v.support*w.power l) := by rw [mul_assoc]
    _ = _ := by rw [(h l).2,← v.add]

theorem difference_square {v w : PartialUnitary A} (h : v≤w) (k : ℤ) :
    star (w.power k-v.power k)*(w.power k-v.power k)=w.support-v.support := by
  rw [star_sub,sub_mul,mul_sub,mul_sub,w.star_power_mul,v.star_power_mul,
    w.power_star,v.power_star,cross_power h,cross_power' h,neg_add_cancel]
  change w.support-v.support-(v.support-v.support)=_
  rw [sub_self,sub_zero]

theorem le_sum (v w : PartialUnitary A) (ho : v.support*w.support=0) : v≤v.sum w ho := by
  intro k
  constructor
  · change (v.power k+w.power k)*v.support=v.power k
    rw [add_mul,v.mul_support]
    change v.power k+w.power k*v.power 0=v.power k
    rw [orthogonal_power w v (orthogonal_symm v w ho),add_zero]
  · change v.support*(v.power k+w.power k)=v.power k
    rw [mul_add,v.support_mul]
    change v.power k+v.power 0*w.power k=v.power k
    rw [orthogonal_power v w ho,add_zero]

theorem zero_le (v : PartialUnitary A) : zero≤v := by
  intro k
  constructor <;> simp [zero,support]

end KKLocalPatching.PartialUnitary
end

end OAI
