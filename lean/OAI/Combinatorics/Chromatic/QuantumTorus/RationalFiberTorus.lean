import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalFiberScale

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
@[reducible] def FiberTorus (_v : Kˣ) (_Ω : M →+ M →+ ℤ) (_α : M →+ ℤ) := M →₀ RatFunc K
namespace FiberTorus
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
instance : AddCommGroup (FiberTorus v Ω α) := inferInstanceAs (AddCommGroup (M →₀ RatFunc K))
def monomial (m : M) (a : RatFunc K) : FiberTorus v Ω α := Finsupp.single m a
def twist (m : M) : RatFunc K →+* RatFunc K := scale (v^(-2*α m))
lemma twist_add (m n : M) (a : RatFunc K) : twist v α (m+n) a=twist v α m (twist v α n a) := by
  change scale (v^(-2*α (m+n))) a=((scale (v^(-2*α m))).comp (scale (v^(-2*α n)))) a
  rw [scale_mul,map_add,mul_add,zpow_add]
@[simp] lemma twist_constant (m : M) (a : K) : twist v α m (RatFunc.C a)=RatFunc.C a := scale_constant _ _
@[simp] lemma twist_zero (a : RatFunc K) : twist v α 0 a=a := by simp [twist]
def multiply (f g : FiberTorus v Ω α) : FiberTorus v Ω α :=
  Finsupp.sum f fun m a=>Finsupp.sum g fun n b=>
    Finsupp.single (m+n) (a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K))
instance : Mul (FiberTorus v Ω α) := ⟨multiply v Ω α⟩
instance : One (FiberTorus v Ω α) := ⟨monomial v Ω α 0 1⟩
@[simp] lemma monomial_zero (m : M) : monomial v Ω α m 0=0 := Finsupp.single_zero _
@[simp] lemma monomial_add (m : M) (a b : RatFunc K) :
    monomial v Ω α m (a+b)=monomial v Ω α m a+monomial v Ω α m b := Finsupp.single_add ..
@[simp] lemma mul_zero (f : FiberTorus v Ω α) : f*0=0 := by simp [HMul.hMul,Mul.mul,multiply]
@[simp] lemma zero_mul (f : FiberTorus v Ω α) : (0 : FiberTorus v Ω α)*f=0 := by simp [HMul.hMul,Mul.mul,multiply]
lemma add_mul (f g h : FiberTorus v Ω α) : (f+g)*h=f*h+g*h := by
  classical
  change multiply v Ω α (f+g) h=multiply v Ω α f h+multiply v Ω α g h
  simp only [multiply]
  rw [Finsupp.sum_add_index']
  · intro m; simp
  · intro m a b
    simp only [_root_.add_mul,Finsupp.single_add,Finsupp.sum_add]
lemma mul_add (f g h : FiberTorus v Ω α) : f*(g+h)=f*g+f*h := by
  classical
  change multiply v Ω α f (g+h)=multiply v Ω α f g+multiply v Ω α f h
  simp only [multiply]
  rw [←Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro m ha
  rw [Finsupp.sum_add_index']
  · intro n; simp
  · intro n a b
    simp only [map_add,_root_.mul_add,_root_.add_mul,Finsupp.single_add]
@[simp] lemma monomial_mul (m n : M) (a b : RatFunc K) :
    monomial v Ω α m a*monomial v Ω α n b=
      monomial v Ω α (m+n) (a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K)) := by
  classical
  change multiply v Ω α (Finsupp.single m a) (Finsupp.single n b)=_
  simp only [multiply,monomial,Finsupp.sum_single_index,MulZeroClass.zero_mul,
    MulZeroClass.mul_zero,map_zero,Finsupp.single_zero]
lemma mul_assoc (f g h : FiberTorus v Ω α) : (f*g)*h=f*(g*h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,add_mul,hg,hg']
    | single n b=>
      induction h using Finsupp.induction_linear with
      | zero=>simp
       | add h h' hh hh'=>simp only [mul_add,hh,hh']
      | single p c=>
        change (monomial v Ω α m a*monomial v Ω α n b)*monomial v Ω α p c=
          monomial v Ω α m a*(monomial v Ω α n b*monomial v Ω α p c)
        simp only [monomial_mul,map_add,AddMonoidHom.add_apply,add_assoc]
        congr 1
        simp only [zpow_add,Units.val_mul,map_mul,twist_constant,twist_add]
        ring
@[simp] lemma one_mul (f : FiberTorus v Ω α) : (1 : FiberTorus v Ω α)*f=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>rw [mul_add,hf,hg]
  | single m a=>
    change monomial v Ω α 0 1*monomial v Ω α m a=monomial v Ω α m a
    simp only [monomial_mul,map_zero,AddMonoidHom.zero_apply,zero_add,
      _root_.one_mul,zpow_zero,Units.val_one,map_one,_root_.mul_one,twist_zero]
@[simp] lemma mul_one (f : FiberTorus v Ω α) : f*(1 : FiberTorus v Ω α)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>rw [add_mul,hf,hg]
  | single m a=>
    change monomial v Ω α m a*monomial v Ω α 0 1=monomial v Ω α m a
    simp only [monomial_mul,map_zero,add_zero,_root_.mul_one,zpow_zero,Units.val_one,map_one]
instance : Ring (FiberTorus v Ω α) :=
  Ring.ofMinimalAxioms _root_.add_assoc _root_.zero_add _root_.neg_add_cancel
    (mul_assoc v Ω α) (one_mul v Ω α) (mul_one v Ω α) (mul_add v Ω α) (add_mul v Ω α)
def coefficient (a : RatFunc K) : FiberTorus v Ω α := monomial v Ω α 0 a
def X (m : M) : FiberTorus v Ω α := monomial v Ω α m 1
lemma rational_commutation (m : M) (f : RatFunc K) :
    X v Ω α m*coefficient v Ω α f=coefficient v Ω α (twist v α m f)*X v Ω α m := by
  simp [X,coefficient,monomial_mul]
end FiberTorus
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
def off : M →+ k.ker where
  toFun m:=⟨m-(k m) • p,by simp [map_sub,map_zsmul,hp]⟩
  map_zero':=by ext; simp
  map_add' m n:=by ext; simp [map_add,add_smul]; abel
@[simp] lemma off_val (m : M) : (off k p hp m : M)=m-k m • p := rfl
lemma split_sum (m : M) : k m • p+(off k p hp m : M)=m := by rw [off_val]; abel
@[simp] lemma off_p : off k p hp p=0 := by ext; simp [hp]
@[simp] lemma off_complement (m : k.ker) : off k p hp m=m := by
  ext
  have hm : k m=0:=m.property
  simp [hm]
def complementAlpha (Ω : M →+ M →+ ℤ) : k.ker →+ ℤ := (Ω p).comp k.ker.subtype
def complementOmega (Ω : M →+ M →+ ℤ) : k.ker →+ k.ker →+ ℤ where
  toFun m:=(Ω m).comp k.ker.subtype
  map_zero':=by ext; simp
  map_add' m n:=by ext; simp
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma split_pairing (m n : M) : Ω m n=
    k m*complementAlpha k p Ω (off k p hp n)-
      k n*complementAlpha k p Ω (off k p hp m)+
      complementOmega k Ω (off k p hp m) (off k p hp n) := by
  have hs (a b : M) : Ω a b= -Ω b a := by
    have H:=hΩ (a+b)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  change Ω m n=k m*Ω p (off k p hp n)-k n*Ω p (off k p hp m)+
    Ω (off k p hp m : M) (off k p hp n : M)
  conv_lhs=>rw [←split_sum k p hp m,←split_sum k p hp n]
  simp only [map_add,AddMonoidHom.add_apply,map_zsmul,AddMonoidHom.zsmul_apply,hΩ,
    smul_eq_mul]
  rw [hs (off k p hp m : M) p]
  ring

def centeredScalar (v : Kˣ) (n a : ℤ) : RatFunc K :=
  RatFunc.C (↑(v^(-n*a)):K)*RatFunc.X^n
lemma centeredScalar_mul (v : Kˣ) (n l a b c : ℤ) :
    centeredScalar v n a*scale (v^(-2*a)) (centeredScalar v l b)*
      RatFunc.C (↑(v^c):K)=
    RatFunc.C (↑(v^(n*b-l*a+c)):K)*centeredScalar v (n+l) (a+b) := by
  have hv : (v:K)≠0:=Units.ne_zero v
  have hz : (RatFunc.X : RatFunc K)≠0:=RatFunc.X_ne_zero
  simp only [centeredScalar,map_mul,scale_constant,map_zpow₀,scale_X,mul_zpow]
  simp only [←map_zpow₀,←Units.val_zpow_eq_zpow_val,←zpow_mul]
  have hleft :
      RatFunc.C (↑(v^(-n*a)):K)*RatFunc.X^n*
        (RatFunc.C (↑(v^(-l*b)):K)*(RatFunc.C (↑(v^(-2*a*l)):K)*RatFunc.X^l))*
        RatFunc.C (↑(v^c):K)=
      RatFunc.C (↑(v^(-n*a)):K)*RatFunc.C (↑(v^(-l*b)):K)*
        RatFunc.C (↑(v^(-2*a*l)):K)*RatFunc.C (↑(v^c):K)*
        (RatFunc.X^n*RatFunc.X^l) := by ring
  rw [hleft,←map_mul,←map_mul,←map_mul,←Units.val_mul,←Units.val_mul,←Units.val_mul,
    ←zpow_add,←zpow_add,←zpow_add,←zpow_add₀ hz]
  rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_add]
  congr 3
  ring_nf
end
end ElementaryPositivity.RationalFiber

end

end OAI
