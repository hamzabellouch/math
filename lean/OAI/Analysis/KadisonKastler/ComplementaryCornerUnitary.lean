import OAI.Analysis.KadisonKastler.TwoCornerStateNorm
import OAI.Analysis.FactorGeneration.PartialIsometries

namespace OAI

/-! # Joining unitaries on complementary projection corners

The two corner conjugations used in state homogeneity join to one actual
unitary. Its two compressions remain exactly the specified corner maps.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem complementary_corner_sum_unitary (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val)
    (hv : star v*v = 1-p.val) (hv' : v*star v = 1-p.val) :
    u+v ∈ unitary (Algebra M) := by
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let a : PartialIsometry M := ⟨p,u,hu⟩
  let b : PartialIsometry M := ⟨q,v,hv⟩
  have hat : a.target = p := Subtype.ext hu'
  have hbt : b.target = q := Subtype.ext hv'
  have hpq : a.support.val*b.support.val = 0 := p.property.mul_one_sub_self
  have ht : a.target.val*b.target.val = 0 := by rw [hat,hbt]; exact hpq
  constructor
  · have hi := (a.patch b hpq ht).initial
    change star (u+v)*(u+v) = _ at hi
    exact hi.trans (by change p.val+(1-p.val)=1; abel)
  · have hi := a.patch_target b hpq ht
    change (u+v)*star (u+v) = _ at hi
    rw [hat,hbt] at hi
    exact hi.trans (by change p.val+(1-p.val)=1; abel)

def complementaryCornerUnitary (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val)
    (hv : star v*v = 1-p.val) (hv' : v*star v = 1-p.val) : unitary (Algebra M) :=
  ⟨u+v,complementary_corner_sum_unitary p u v hu hu' hv hv'⟩

theorem cornerUnitary_supports (p : AlgebraProjection M)
    (u : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val) :
    p.val*u = u ∧ u*p.val = u := by
  let a : PartialIsometry M := ⟨p,u,hu⟩
  have hat : a.target = p := Subtype.ext hu'
  exact ⟨hat ▸ a.target_mul,a.mul_support⟩

theorem complementaryCornerUnitary_compressions (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val)
    (hv : star v*v = 1-p.val) (hv' : v*star v = 1-p.val) :
    p.val*(u+v) = u ∧ (u+v)*p.val = u ∧
      (1-p.val)*(u+v) = v ∧ (u+v)*(1-p.val) = v := by
  obtain ⟨hpu,hup⟩ := cornerUnitary_supports p u hu hu'
  obtain ⟨hqv,hvq⟩ := cornerUnitary_supports ⟨1-p.val,p.property.one_sub⟩ v hv hv'
  change (1-p.val)*v=v at hqv
  change v*(1-p.val)=v at hvq
  have hpv : p.val*v=0 := by rw [sub_mul,one_mul] at hqv; exact sub_eq_self.mp hqv
  have hvp : v*p.val=0 := by rw [mul_sub,mul_one] at hvq; exact sub_eq_self.mp hvq
  have hqu : (1-p.val)*u=0 := by rw [sub_mul,one_mul,hpu,sub_self]
  have huq : u*(1-p.val)=0 := by rw [mul_sub,mul_one,hup,sub_self]
  simp only [mul_add,add_mul,hpu,hup,hpv,hvp,hqu,huq,hqv,hvq,zero_add,add_zero]
  trivial

theorem complementary_corner_conjugation (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val)
    (hv : star v*v = 1-p.val) (hv' : v*star v = 1-p.val) (x : Algebra M) :
    p.val*(star (u+v)*x*(u+v))*p.val = star u*x*u ∧
      (1-p.val)*(star (u+v)*x*(u+v))*(1-p.val) = star v*x*v := by
  obtain ⟨hpu,hup,hqv,hvq⟩ :=
    complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  have hps : p.val*star (u+v)=star u := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hup
  have hqs : (1-p.val)*star (u+v)=star v := by
    simpa only [star_mul,star_sub,star_one,p.property.isSelfAdjoint.star_eq]
      using congrArg star hvq
  constructor
  · calc
      _ = (p.val*star (u+v))*x*((u+v)*p.val) := by simp only [mul_assoc]
      _ = _ := by rw [hps,hup]
  · calc
      _ = ((1-p.val)*star (u+v))*x*((u+v)*(1-p.val)) := by simp only [mul_assoc]
      _ = _ := by rw [hqs,hvq]

end

end KadisonKastler

end OAI
