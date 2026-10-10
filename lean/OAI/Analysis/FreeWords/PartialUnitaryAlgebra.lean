import Mathlib

namespace OAI

noncomputable section

namespace KKLocalPatching

structure PartialUnitary (A : Type*) [Ring A] [StarRing A] where
  power : ℤ → A
  add : ∀ k l, power (k+l)=power k*power l
  power_star : ∀ k, star (power k)=power (-k)

namespace PartialUnitary

variable {A : Type*} [Ring A] [StarRing A]

def support (v : PartialUnitary A) : A := v.power 0

@[simp] theorem support_mul (v : PartialUnitary A) (k : ℤ) : v.support*v.power k=v.power k := by
  rw [support,← v.add,zero_add]

@[simp] theorem mul_support (v : PartialUnitary A) (k : ℤ) : v.power k*v.support=v.power k := by
  rw [support,← v.add,add_zero]

theorem projection (v : PartialUnitary A) : IsStarProjection v.support := by
  constructor
  · exact v.mul_support 0
  · change star (v.power 0)=v.power 0
    rw [v.power_star,neg_zero]

@[simp] theorem star_power_mul (v : PartialUnitary A) (k : ℤ) : star (v.power k)*v.power k=v.support := by
  rw [v.power_star,← v.add,neg_add_cancel]
  rfl

@[simp] theorem power_mul_star (v : PartialUnitary A) (k : ℤ) : v.power k*star (v.power k)=v.support := by
  rw [v.power_star,← v.add,add_neg_cancel]
  rfl

def zero : PartialUnitary A where
  power _ := 0
  add _ _ := (zero_mul _).symm
  power_star _ := star_zero A

theorem orthogonal_power (v w : PartialUnitary A) (ho : v.support*w.support=0) (k l : ℤ) :
    v.power k*w.power l=0 := by
  calc
    _ = (v.power k*v.support)*(w.support*w.power l) := by simp
    _ = v.power k*(v.support*w.support)*w.power l := by noncomm_ring
    _ = 0 := by rw [ho,mul_zero,zero_mul]

theorem orthogonal_symm (v w : PartialUnitary A) (ho : v.support*w.support=0) :
    w.support*v.support=0 := by
  have h := congrArg star ho
  simpa only [star_mul,(v.projection).isSelfAdjoint.star_eq,
    (w.projection).isSelfAdjoint.star_eq,star_zero] using h

def sum (v w : PartialUnitary A) (ho : v.support*w.support=0) : PartialUnitary A where
  power k := v.power k+w.power k
  add k l := by
    rw [v.add,w.add,add_mul,mul_add,mul_add,orthogonal_power v w ho,
      orthogonal_power w v (orthogonal_symm v w ho),add_zero,zero_add]
  power_star k := by rw [star_add,v.power_star,w.power_star]

@[simp] theorem sum_power (v w : PartialUnitary A) (ho) (k : ℤ) :
    (v.sum w ho).power k=v.power k+w.power k := rfl

@[simp] theorem sum_support (v w : PartialUnitary A) (ho) :
    (v.sum w ho).support=v.support+w.support := rfl

def toUnitary (v : PartialUnitary A) (hv : v.support=1) : unitary A :=
  ⟨v.power 1, by constructor <;> simp only [star_power_mul,power_mul_star,hv]⟩

theorem toUnitary_power (v : PartialUnitary A) (hv : v.support=1) (k : ℤ) :
    ((v.toUnitary hv)^k).val=v.power k := by
  let f : Multiplicative ℤ →* unitary A :=
    { toFun k := ⟨v.power k.toAdd, by constructor <;> simp only [star_power_mul,power_mul_star,hv]⟩
      map_one' := Subtype.ext hv
      map_mul' k l := Subtype.ext (v.add k.toAdd l.toAdd) }
  have h := congrArg Subtype.val (f.map_zpow (Multiplicative.ofAdd 1) k)
  change v.power (k • (1:ℤ))=((v.toUnitary hv)^k).val at h
  simpa only [smul_eq_mul,mul_one] using h.symm

end PartialUnitary

end KKLocalPatching
end

end OAI
