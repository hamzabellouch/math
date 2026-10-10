import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalFiberTorus
import OAI.Combinatorics.Chromatic.Walls.RationalFiberReciprocal
import OAI.Combinatorics.Chromatic.Walls.LaurentRayEmbedding

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K : Type*} [Field K]
lemma ratFunc_hom_ext_ring {A : Type*} [Ring A] (f g : RatFunc K →+* A)
    (hpoly : ∀p : Polynomial K,f (algebraMap (Polynomial K) (RatFunc K) p)=
      g (algebraMap (Polynomial K) (RatFunc K) p)) : f=g := by
  apply RingHom.ext
  intro x
  induction x using RatFunc.induction_on with
  | f p q hq=>
    have hu : IsUnit (f (algebraMap (Polynomial K) (RatFunc K) q)):=
      (isUnit_iff_ne_zero.mpr (RatFunc.algebraMap_ne_zero hq)).map f
    apply hu.mul_right_cancel
    rw [←map_mul,div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq),hpoly p,hpoly q,
      ←map_mul,div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq)]
def innerHom {A : Type*} [Ring A] (u : Aˣ) : A →+* A where
  toFun a:=(↑u:A)*a*(↑(u⁻¹):A)
  map_zero':=by simp
  map_one':=by simp
  map_add' a b:=by simp [mul_add,add_mul]
  map_mul' a b:=by simp [mul_assoc]
variable {M : Type*} [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def expandScalar : RatFunc K →+* HahnSeries ℤ (Torus v Ω) :=
  (laurentRayHom v Ω p (hΩ p)).comp expandZero
lemma expandScalar_C (a : K) :
    expandScalar v Ω hΩ p (RatFunc.C a)=HahnSeries.single 0 (Torus.monomial v Ω 0 a) := by
  simp only [expandScalar,RingHom.comp_apply,expandZero_constant]
  change laurentRay v Ω p (HahnSeries.single 0 a)=_
  rw [laurentRay_single,zero_smul]
lemma expandScalar_X : expandScalar v Ω hΩ p RatFunc.X=HahnSeries.single 1 (Torus.X v Ω p) := by
  change laurentRay v Ω p (expandZero RatFunc.X)=_
  have H:=expandZero_X_zpow (K:=K) (1:ℤ)
  simp only [zpow_one] at H
  rw [H,laurentRay_single,one_smul]
  rfl
include hΩ in
lemma torus_X_unit (m : M) : Torus.X v Ω m*Torus.X v Ω (-m)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω m (-m) (by simp [hΩ]),add_neg_cancel,Torus.X_zero]
def constUnit (m : M) : (HahnSeries ℤ (Torus v Ω))ˣ where
  val:=HahnSeries.single 0 (Torus.X v Ω m)
  inv:=HahnSeries.single 0 (Torus.X v Ω (-m))
  val_inv:=by rw [HahnSeries.single_mul_single,zero_add,torus_X_unit v Ω hΩ]; rfl
  inv_val:=by
    rw [HahnSeries.single_mul_single,zero_add]
    have H:=torus_X_unit v Ω hΩ (-m)
    simpa using congrArg (HahnSeries.single (0:ℤ)) H
include hΩ in
lemma pairing_swap (a b : M) : Ω a b= -Ω b a := by
  have H:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
  omega
lemma constUnit_conj_C (m : M) (a : K) :
    innerHom (constUnit v Ω hΩ m) (expandScalar v Ω hΩ p (RatFunc.C a))=
      expandScalar v Ω hΩ p (RatFunc.C a) := by
  rw [expandScalar_C]
  dsimp only [innerHom, constUnit, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk, Units.inv_mk]
  rw [HahnSeries.single_mul_single,HahnSeries.single_mul_single]
  simp [Torus.X,Torus.monomial_mul_monomial,hΩ]
lemma constUnit_conj_X (m : M) :
    innerHom (constUnit v Ω hΩ m) (expandScalar v Ω hΩ p RatFunc.X)=
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(-2*Ω p m)):K)*RatFunc.X) := by
  rw [map_mul,expandScalar_C,expandScalar_X]
  dsimp only [innerHom, constUnit, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk, Units.inv_mk]
  simp only [HahnSeries.single_mul_single,zero_add,add_zero,Torus.X,Torus.monomial_mul_monomial,
    map_add,AddMonoidHom.add_apply,map_neg,hΩ,map_zero,AddMonoidHom.zero_apply,
    zpow_zero,Units.val_one,mul_one,one_mul,zero_add]
  have he : m+p+-m=p:=by abel
  rw [he,←Units.val_mul,←zpow_add,pairing_swap Ω hΩ m p]
  congr 3
  ring_nf
lemma scalar_commutation (m : M) (a : RatFunc K) :
    HahnSeries.single 0 (Torus.X v Ω m)*expandScalar v Ω hΩ p a=
      expandScalar v Ω hΩ p (scale (v^(-2*Ω p m)) a)*HahnSeries.single 0 (Torus.X v Ω m) := by
  have HE : (innerHom (constUnit v Ω hΩ m)).comp (expandScalar v Ω hΩ p)=
      (expandScalar v Ω hΩ p).comp (scale (v^(-2*Ω p m))) := by
    apply ratFunc_hom_ext_ring
    have HP : ((innerHom (constUnit v Ω hΩ m)).comp (expandScalar v Ω hΩ p)).comp
        (algebraMap (Polynomial K) (RatFunc K))=
        ((expandScalar v Ω hΩ p).comp (scale (v^(-2*Ω p m)))).comp
        (algebraMap (Polynomial K) (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro a
        change innerHom _ (expandScalar v Ω hΩ p (RatFunc.C a))=
          expandScalar v Ω hΩ p (scale _ (RatFunc.C a))
        rw [scale_constant,constUnit_conj_C]
      · change innerHom _ (expandScalar v Ω hΩ p RatFunc.X)=
          expandScalar v Ω hΩ p (scale _ RatFunc.X)
        rw [scale_X,constUnit_conj_X]
    exact fun q=>congrArg (fun f : Polynomial K →+* HahnSeries ℤ (Torus v Ω)=>f q) HP
  have H:=congrArg (fun f : RatFunc K →+* HahnSeries ℤ (Torus v Ω)=>f a) HE
  change ↑(constUnit v Ω hΩ m)*expandScalar v Ω hΩ p a*↑((constUnit v Ω hΩ m)⁻¹)=
    expandScalar v Ω hΩ p (scale _ a) at H
  have HH:=congrArg (fun x : HahnSeries ℤ (Torus v Ω)=>x*(↑(constUnit v Ω hΩ m):HahnSeries ℤ (Torus v Ω))) H
  have hu : (↑((constUnit v Ω hΩ m)⁻¹):HahnSeries ℤ (Torus v Ω))*↑(constUnit v Ω hΩ m)=1 := (constUnit v Ω hΩ m).inv_val
  rw [mul_assoc, mul_assoc, hu, mul_one] at HH
  exact HH
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def expandFiberTerm (l : k.ker) : RatFunc K →+ HahnSeries ℤ (Torus v Ω) where
  toFun a:=expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l)
  map_zero':=by simp
  map_add' a b:=by simp [add_mul]
def expandFiberAdd : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+
    HahnSeries ℤ (Torus v Ω) := Finsupp.liftAddHom (expandFiberTerm v Ω hΩ k p)
lemma expandFiberAdd_monomial (l : k.ker) (a : RatFunc K) :
    expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)=
      expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma const_torus_product (m n : M) :
    HahnSeries.single (0:ℤ) (Torus.X v Ω m)*HahnSeries.single 0 (Torus.X v Ω n)=
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(Ω m n)):K))*
        HahnSeries.single 0 (Torus.X v Ω (m+n)) := by
  rw [expandScalar_C]
  simp [HahnSeries.single_mul_single,Torus.X,Torus.monomial_mul_monomial]
lemma expandFiberAdd_monomial_mul (l j : k.ker) (a b : RatFunc K) :
    expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a*FiberTorus.monomial v _ _ j b)=
      expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)*
        expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ j b) := by
  rw [FiberTorus.monomial_mul,expandFiberAdd_monomial,expandFiberAdd_monomial,expandFiberAdd_monomial]
  simp only [_root_.map_mul,FiberTorus.twist]
  change (expandScalar v Ω hΩ p a*expandScalar v Ω hΩ p (scale (v^(-2*Ω p l)) b)*
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(Ω l j)):K)))*
      HahnSeries.single 0 (Torus.X v Ω ((l:M)+(j:M)))=_
  simp only [mul_assoc]
  rw [←const_torus_product]
  rw [←mul_assoc (expandScalar v Ω hΩ p (scale _ b)),←scalar_commutation]
  simp only [mul_assoc]

lemma expandFiberAdd_mul (f g : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiberAdd v Ω hΩ k p (f*g)=expandFiberAdd v Ω hΩ k p f*expandFiberAdd v Ω hΩ k p g := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [_root_.add_mul,map_add,hf,hf']
  | single l a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [_root_.mul_add,map_add,hg,hg']
    | single j b=>exact expandFiberAdd_monomial_mul v Ω hΩ k p l j a b
lemma expandFiberAdd_one : expandFiberAdd v Ω hΩ k p 1=1 := by
  change expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ 0 1)=_
  rw [expandFiberAdd_monomial,map_one,one_mul]
  rfl
def expandFiber : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    HahnSeries ℤ (Torus v Ω) where
  __:=expandFiberAdd v Ω hΩ k p
  map_one':=expandFiberAdd_one v Ω hΩ k p
  map_mul':=expandFiberAdd_mul v Ω hΩ k p
end
end ElementaryPositivity.RationalFiber

end

end OAI
