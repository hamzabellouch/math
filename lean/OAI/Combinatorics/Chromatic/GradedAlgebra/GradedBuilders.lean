import Mathlib

namespace OAI

section
namespace ElementaryPositivity

@[instance_reducible]
noncomputable def gradedMonoidOfLaws {J : Type*} [AddMonoid J] {A : J → Type*}
    [GradedMonoid.GMul A] [GradedMonoid.GOne A]
    (h₁ : ∀ x : GradedMonoid A,1*x=x)
    (h₂ : ∀ x : GradedMonoid A,x*1=x)
    (h₃ : ∀ x y z : GradedMonoid A,x*y*z=x*(y*z)) : GradedMonoid.GMonoid A where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul := h₁
  mul_one := h₂
  mul_assoc := h₃

@[instance_reducible]
noncomputable def gradedRingOfAddLaws {J : Type*} [AddMonoid J] {A : J → Type*}
    [∀ j,AddCommGroup (A j)] [GradedMonoid.GMonoid A]
    (hzr : ∀ {i j} (x : A i),GradedMonoid.GMul.mul x (0 : A j)=0)
    (hzl : ∀ {i j} (x : A j),GradedMonoid.GMul.mul (0 : A i) x=0)
    (har : ∀ {i j} (x : A i) (y z : A j),
      GradedMonoid.GMul.mul x (y+z)=GradedMonoid.GMul.mul x y+GradedMonoid.GMul.mul x z)
    (hal : ∀ {i j} (x y : A i) (z : A j),
      GradedMonoid.GMul.mul (x+y) z=GradedMonoid.GMul.mul x z+GradedMonoid.GMul.mul y z) :
    DirectSum.GRing A where
  toGMonoid := inferInstance
  mul_zero := hzr
  zero_mul := hzl
  mul_add := har
  add_mul := hal
  natCast n := n • GradedMonoid.GOne.one
  natCast_zero := zero_nsmul _
  natCast_succ n := by rw [add_nsmul,one_nsmul]
  intCast n := n • GradedMonoid.GOne.one
  intCast_ofNat n := by simp only [natCast_zsmul]
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

@[instance_reducible]
noncomputable def gradedAlgebraOfBilinear {J R : Type*} [AddMonoid J] [CommSemiring R]
    {A : J → Type*} [∀ j,AddCommMonoid (A j)] [∀ j,Module R (A j)]
    [DirectSum.GSemiring A]
    (hl : ∀ (r : R) (x y : GradedMonoid A),(r•x)*y=r•(x*y))
    (hr : ∀ (r : R) (x y : GradedMonoid A),x*(r•y)=r•(x*y)) :
    DirectSum.GAlgebra R A where
  toFun := (LinearMap.toSpanSingleton R (A 0) GradedMonoid.GOne.one).toAddMonoidHom
  map_one := one_smul R _
  map_mul r s := by
    change (r*s) • (1 : GradedMonoid A) = (r • (1 : GradedMonoid A)) * (s • (1 : GradedMonoid A))
    rw [hl,hr,one_mul,smul_smul]
  commutes r x := by
    change (r • (1 : GradedMonoid A))*x=x*(r • (1 : GradedMonoid A))
    rw [hl,hr,one_mul,mul_one]
  smul_def r x := by
    change r•x=(r • (1 : GradedMonoid A))*x
    rw [hl,one_mul]

end ElementaryPositivity

end

end OAI
