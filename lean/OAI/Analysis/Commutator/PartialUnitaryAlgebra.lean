import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

structure PartialUnitary where
  val : A
  support : A
  projection : IsStarProjection support
  star_mul : star val*val=support
  mul_star : val*star val=support
  mul_support : val*support=val
  support_mul : support*val=val

namespace PartialUnitary

variable {A}

lemma norm_le_one (v : PartialUnitary A) : ‖v.val‖ ≤ 1 := by
  have h := v.projection.norm_le v.support
  rw [←v.star_mul,CStarRing.norm_star_mul_self] at h
  nlinarith [_root_.norm_nonneg v.val]

@[simp] lemma star_mul_support (v : PartialUnitary A) : star v.val*v.support=star v.val := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,star_star] using
    congrArg star v.support_mul

@[simp] lemma support_mul_star (v : PartialUnitary A) : v.support*star v.val=star v.val := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,star_star] using
    congrArg star v.mul_support

def power (v : PartialUnitary A) : ℤ → A
  | .ofNat 0 => v.support
  | .ofNat (n+1) => v.val^(n+1)
  | .negSucc n => (star v.val)^(n+1)

@[simp] lemma power_zero (v : PartialUnitary A) : v.power 0=v.support := rfl

@[simp] lemma power_nat_succ (v : PartialUnitary A) (n : ℕ) :
    v.power (n+1 : ℕ)=v.val^(n+1) := rfl

@[simp] lemma power_negSucc (v : PartialUnitary A) (n : ℕ) :
    v.power (.negSucc n)=(star v.val)^(n+1) := rfl

lemma power_support (v : PartialUnitary A) (k : ℤ) : v.power k*v.support=v.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.isIdempotentElem.eq
    | succ n =>
      simp only [power,pow_succ,mul_assoc,v.mul_support]
  | negSucc n => simp only [power,pow_succ,mul_assoc,v.star_mul_support]

lemma support_power (v : PartialUnitary A) (k : ℤ) : v.support*v.power k=v.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.isIdempotentElem.eq
    | succ n => simp only [power,pow_succ',←mul_assoc,v.support_mul]
  | negSucc n => simp only [power,pow_succ',←mul_assoc,v.support_mul_star]

lemma power_norm (v : PartialUnitary A) (k : ℤ) : ‖v.power k‖ ≤ 1 := by
  have hp (a : A) (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a^(n+1)‖ ≤ 1 :=
    (norm_pow_le' a (Nat.succ_pos n)).trans (pow_le_one₀ (_root_.norm_nonneg _) ha)
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.norm_le _
    | succ n => exact hp _ v.norm_le_one _
  | negSucc n => exact hp _ (by simpa using v.norm_le_one) _

lemma star_power (v : PartialUnitary A) (k : ℤ) : star (v.power k)=v.power (-k) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.isSelfAdjoint.star_eq
    | succ n => simp only [power,star_pow]; rfl
  | negSucc n => simp only [power,star_pow,star_star]; rfl

lemma orthogonal_support_symm {v w : PartialUnitary A}
    (h : v.support*w.support=0) : w.support*v.support=0 := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,w.projection.isSelfAdjoint.star_eq,
    star_zero] using congrArg star h

lemma power_mul_power_zero {v w : PartialUnitary A} (h : v.support*w.support=0)
    (k l : ℤ) : v.power k*w.power l=0 := by
  calc
    _=(v.power k*v.support)*(w.support*w.power l) := by rw [power_support,support_power]
    _=0 := by rw [mul_assoc,←mul_assoc v.support,h,zero_mul,mul_zero]

lemma val_mul_zero {v w : PartialUnitary A} (h : v.support*w.support=0) : v.val*w.val=0 :=
  by simpa [power] using power_mul_power_zero h 1 1

lemma star_val_mul_zero {v w : PartialUnitary A} (h : v.support*w.support=0) :
    star v.val*w.val=0 := by simpa [power] using power_mul_power_zero h (Int.negSucc 0) 1

lemma val_mul_star_zero {v w : PartialUnitary A} (h : v.support*w.support=0) :
    v.val*star w.val=0 := by simpa [power] using power_mul_power_zero h 1 (Int.negSucc 0)

def add (v w : PartialUnitary A) (h : v.support*w.support=0) : PartialUnitary A where
  val := v.val+w.val
  support := v.support+w.support
  projection := by
    constructor
    · dsimp [IsIdempotentElem]
      rw [add_mul,mul_add,mul_add,v.projection.isIdempotentElem.eq,
        w.projection.isIdempotentElem.eq,h,orthogonal_support_symm h]
      simp
    · exact v.projection.isSelfAdjoint.add w.projection.isSelfAdjoint
  star_mul := by
    rw [star_add,add_mul,mul_add,mul_add,v.star_mul,w.star_mul,
      star_val_mul_zero h,star_val_mul_zero (orthogonal_support_symm h)]
    simp
  mul_star := by
    rw [star_add,add_mul,mul_add,mul_add,v.mul_star,w.mul_star,
      val_mul_star_zero h,val_mul_star_zero (orthogonal_support_symm h)]
    simp
  mul_support := by
    have h1 := power_mul_power_zero h 1 0
    have h2 := power_mul_power_zero (orthogonal_support_symm h) 1 0
    simp [power] at h1 h2
    rw [add_mul,mul_add,mul_add,v.mul_support,w.mul_support,h1,h2]
    simp
  support_mul := by
    have h1 := power_mul_power_zero h 0 1
    have h2 := power_mul_power_zero (orthogonal_support_symm h) 0 1
    simp [power] at h1 h2
    rw [add_mul,mul_add,mul_add,v.support_mul,w.support_mul,h1,h2]
    simp

lemma pow_add_of_mul_zero {a b : A} (hab : a*b=0) (hba : b*a=0) (n : ℕ) :
    (a+b)^(n+1)=a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a^(n+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h2 : b^(n+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [pow_succ,ih,add_mul,mul_add,mul_add,h1,h2]
    simp only [add_zero,zero_add,←pow_succ]

lemma add_power (v w : PartialUnitary A) (h : v.support*w.support=0) (k : ℤ) :
    (v.add w h).power k=v.power k+w.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      exact pow_add_of_mul_zero (val_mul_zero h) (val_mul_zero (orthogonal_support_symm h)) n
  | negSucc n =>
    change (star (v.val+w.val))^(n+1)=(star v.val)^(n+1)+(star w.val)^(n+1)
    rw [star_add]
    apply pow_add_of_mul_zero
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero (orthogonal_support_symm h))
    · simpa only [StarMul.star_mul,star_zero] using congrArg star (val_mul_zero h)

def zero : PartialUnitary A where
  val := 0
  support := 0
  projection := IsStarProjection.zero A
  star_mul := by simp
  mul_star := by simp
  mul_support := by simp
  support_mul := by simp

@[simp] lemma zero_power (k : ℤ) : (zero : PartialUnitary A).power k=0 := by
  cases k with
  | ofNat n => cases n <;> simp [power,zero]
  | negSucc n => simp [power,zero]

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
