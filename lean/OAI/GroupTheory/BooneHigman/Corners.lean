import OAI.GroupTheory.BooneHigman.MonoidAlgebras
import OAI.GroupTheory.BooneHigman.Enveloping

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

def U : monoid := wordValue [0]
def V : monoid := wordValue [1]
def UI : monoid := wordValue [2]
def VI : monoid := wordValue [3]
def E0 : monoid := wordValue [4]
def E1 : monoid := wordValue [5]
def Eh : monoid := U*E1*UI

@[simp] theorem U_apply (o : Option ℚ) : U.val o=o.map (fun x => x/2) := by
  simpa [U,wordValue,value] using generator_u o
@[simp] theorem V_apply (o : Option ℚ) : V.val o=o.map (fun x => (x+1)/2) := by
  simpa [V,wordValue,value] using generator_v o
@[simp] theorem UI_apply (o : Option ℚ) : UI.val o=o.map (fun x => 2*x) := by
  simpa [UI,wordValue,value] using generator_ui o
@[simp] theorem VI_apply (o : Option ℚ) : VI.val o=o.map (fun x => 2*x-1) := by
  simpa [VI,wordValue,value] using generator_vi o
@[simp] theorem E0_val : E0.val=tail 0 := by
  simpa [E0,wordValue,value] using generator_tail0
@[simp] theorem E1_val : E1.val=tail 1 := by
  simpa [E1,wordValue,value] using generator_tail1

@[simp] theorem U_UI : U*UI=1 := by
  apply Subtype.ext
  funext o
  change U.val (UI.val o)=o
  cases o <;> simp
@[simp] theorem UI_U : UI*U=1 := by
  apply Subtype.ext
  funext o
  change UI.val (U.val o)=o
  cases o <;> simp
  ring
@[simp] theorem V_VI : V*VI=1 := by
  apply Subtype.ext
  funext o
  change V.val (VI.val o)=o
  cases o <;> simp
@[simp] theorem VI_V : VI*V=1 := by
  apply Subtype.ext
  funext o
  change VI.val (V.val o)=o
  cases o <;> simp
  ring

theorem U_tail (r : ℚ) : U.val*tail r*UI.val=tail (r/2) := by
  funext o
  cases o with
  | none =>
    change U.val ((tail r) (UI.val none))=none
    simp [tail]
  | some x =>
    change U.val ((tail r) (UI.val (some x)))=(tail (r/2)) (some x)
    simp only [UI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x
    · have hr' : r/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬r/2≤x := by linarith
      simp [hr,hr']

theorem V_tail (r : ℚ) : V.val*tail r*VI.val=tail ((r+1)/2) := by
  funext o
  cases o with
  | none =>
    change V.val ((tail r) (VI.val none))=none
    simp [tail]
  | some x =>
    change V.val ((tail r) (VI.val (some x)))=(tail ((r+1)/2)) (some x)
    simp only [VI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x-1
    · have hr' : (r+1)/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬(r+1)/2≤x := by linarith
      simp [hr,hr']

@[simp] theorem Eh_val : Eh.val=tail (1/2) := by
  exact (congrArg (fun e => U.val*e*UI.val) E1_val).trans (U_tail 1)

@[simp] theorem U_E0_UI : U*E0*UI=E0 := by
  apply Subtype.ext
  change U.val*E0.val*UI.val=E0.val
  rw [E0_val,U_tail]
  norm_num
@[simp] theorem U_E1_UI : U*E1*UI=Eh := rfl
@[simp] theorem V_E0_VI : V*E0*VI=Eh := by
  apply Subtype.ext
  change V.val*E0.val*VI.val=Eh.val
  rw [E0_val,Eh_val,V_tail]
  norm_num
@[simp] theorem V_E1_VI : V*E1*VI=E1 := by
  apply Subtype.ext
  change V.val*E1.val*VI.val=E1.val
  rw [E1_val,V_tail]
  norm_num

 theorem tails_mul {a b c : monoid} {r s : ℚ} (ha : a.val=tail r) (hb : b.val=tail s)
    (hc : c.val=tail (max r s)) : a*b=c := by
  apply Subtype.ext
  change a.val*b.val=c.val
  rw [ha,hb,hc,tail_mul]

@[simp] theorem E0_E0 : E0*E0=E0 := tails_mul E0_val E0_val (by simp)
@[simp] theorem E0_Eh : E0*Eh=Eh := tails_mul E0_val Eh_val (by norm_num)
@[simp] theorem E0_E1 : E0*E1=E1 := tails_mul E0_val E1_val (by norm_num)
@[simp] theorem Eh_E0 : Eh*E0=Eh := tails_mul Eh_val E0_val (by norm_num)
@[simp] theorem Eh_Eh : Eh*Eh=Eh := tails_mul Eh_val Eh_val (by simp)
@[simp] theorem Eh_E1 : Eh*E1=E1 := tails_mul Eh_val E1_val (by norm_num)
@[simp] theorem E1_E0 : E1*E0=E1 := tails_mul E1_val E0_val (by norm_num)
@[simp] theorem E1_Eh : E1*Eh=E1 := tails_mul E1_val Eh_val (by norm_num)
@[simp] theorem E1_E1 : E1*E1=E1 := tails_mul E1_val E1_val (by simp)

 theorem E0_ne_E1 : E0≠E1 := by
  intro h
  have hh := congrArg Subtype.val h
  rw [E0_val,E1_val] at hh
  have := tail_injective hh
  norm_num at this
 theorem E0_ne_one : E0≠1 := by
  intro h
  apply tail_ne_one 0
  simpa using congrArg Subtype.val h

end FiniteAlgebraicEnvelopes.PartialAffine

namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open MonoidAlgebra
variable (k : Type*) [CommRing k]

def b (a : monoid) : MonoidAlgebra k monoid := single a 1
@[simp] theorem b_mul (a c : monoid) : b k a*b k c=b k (a*c) := by simp [b,single_mul_single]
@[simp] theorem b_one : b k 1=1 := rfl

def q : MonoidAlgebra k monoid := b k E0-b k E1
def q0 : MonoidAlgebra k monoid := b k E0-b k Eh
def q1 : MonoidAlgebra k monoid := b k Eh-b k E1

theorem q_idem : q k*q k=q k := by
  simp only [q,sub_mul,mul_sub,b_mul,E0_E0,E0_E1,E1_E0,E1_E1]
  abel
 theorem q0_idem : q0 k*q0 k=q0 k := by
  simp only [q0,sub_mul,mul_sub,b_mul,E0_E0,E0_Eh,Eh_E0,Eh_Eh]
  abel
 theorem q1_idem : q1 k*q1 k=q1 k := by
  simp only [q1,sub_mul,mul_sub,b_mul,Eh_Eh,Eh_E1,E1_Eh,E1_E1]
  abel
 theorem q0_q1 : q0 k*q1 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,E0_Eh,E0_E1,Eh_Eh,Eh_E1]
  abel
 theorem q1_q0 : q1 k*q0 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,Eh_E0,Eh_Eh,E1_E0,E1_Eh]
  abel
 theorem q0_add_q1 : q0 k+q1 k=q k := by unfold q0 q1 q; abel
 theorem q_q0 : q k*q0 k=q0 k := by rw [←q0_add_q1,add_mul,q0_idem,q1_q0,add_zero]
 theorem q0_q : q0 k*q k=q0 k := by rw [←q0_add_q1,mul_add,q0_idem,q0_q1,add_zero]
 theorem q_q1 : q k*q1 k=q1 k := by rw [←q0_add_q1,add_mul,q0_q1,q1_idem,zero_add]
 theorem q1_q : q1 k*q k=q1 k := by rw [←q0_add_q1,mul_add,q1_q0,q1_idem,zero_add]

 theorem q_ne_zero [Nontrivial k] : q k≠0 := by
  intro he
  have hh := congrArg (fun f : MonoidAlgebra k monoid => f.coeff E0) he
  simp [q,b,E0_ne_E1] at hh

 theorem q_ne_one [Nontrivial k] : q k≠1 := by
  intro he
  have hh := congrArg (fun f : MonoidAlgebra k monoid => f.coeff E0) he
  simp [q,b,E0_ne_E1,E0_ne_one,MonoidAlgebra.one_def] at hh

def s0 : MonoidAlgebra k monoid := b k U*q k
def s1 : MonoidAlgebra k monoid := b k V*q k
def t0 : MonoidAlgebra k monoid := q k*b k UI
def t1 : MonoidAlgebra k monoid := q k*b k VI

 theorem conjugate0 : b k U*q k*b k UI=q0 k := by
  simp only [q,q0,mul_sub,sub_mul,b_mul,U_E0_UI,U_E1_UI]
 theorem conjugate1 : b k V*q k*b k VI=q1 k := by
  simp only [q,q1,mul_sub,sub_mul,b_mul,V_E0_VI,V_E1_VI]

 theorem t0_s0 : t0 k*s0 k=q k := by
  unfold t0 s0
  calc
    _=q k*(b k UI*b k U)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,UI_U,b_one,mul_one,q_idem]
 theorem t1_s1 : t1 k*s1 k=q k := by
  unfold t1 s1
  calc
    _=q k*(b k VI*b k V)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,VI_V,b_one,mul_one,q_idem]
 theorem s0_t0 : s0 k*t0 k=q0 k := by
  unfold s0 t0
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate0]
 theorem s1_t1 : s1 k*t1 k=q1 k := by
  unfold s1 t1
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate1]

 theorem s0_q : s0 k*q k=s0 k := by unfold s0; rw [mul_assoc,q_idem]
 theorem s1_q : s1 k*q k=s1 k := by unfold s1; rw [mul_assoc,q_idem]
 theorem q_t0 : q k*t0 k=t0 k := by unfold t0; rw [←mul_assoc,q_idem]
 theorem q_t1 : q k*t1 k=t1 k := by unfold t1; rw [←mul_assoc,q_idem]
 theorem q0_s0 : q0 k*s0 k=s0 k := by rw [←s0_t0,mul_assoc,t0_s0,s0_q]
 theorem q1_s1 : q1 k*s1 k=s1 k := by rw [←s1_t1,mul_assoc,t1_s1,s1_q]
 theorem t0_q0 : t0 k*q0 k=t0 k := by rw [←s0_t0,←mul_assoc,t0_s0,q_t0]
 theorem t1_q1 : t1 k*q1 k=t1 k := by rw [←s1_t1,←mul_assoc,t1_s1,q_t1]
 theorem q_s0 : q k*s0 k=s0 k := by nth_rw 1 [←q0_s0 k]; rw [←mul_assoc,q_q0,q0_s0]
 theorem q_s1 : q k*s1 k=s1 k := by nth_rw 1 [←q1_s1 k]; rw [←mul_assoc,q_q1,q1_s1]
 theorem t0_q : t0 k*q k=t0 k := by nth_rw 1 [←t0_q0 k]; rw [mul_assoc,q0_q,t0_q0]
 theorem t1_q : t1 k*q k=t1 k := by nth_rw 1 [←t1_q1 k]; rw [mul_assoc,q1_q,t1_q1]
 theorem t0_s1 : t0 k*s1 k=0 := by
  nth_rw 1 [←t0_q0 k,←q1_s1 k]
  calc
    _=t0 k*(q0 k*q1 k)*s1 k := by simp only [mul_assoc]
    _=0 := by rw [q0_q1,mul_zero,zero_mul]
 theorem t1_s0 : t1 k*s0 k=0 := by
  nth_rw 1 [←t1_q1 k,←q0_s0 k]
  calc
    _=t1 k*(q1 k*q0 k)*s0 k := by simp only [mul_assoc]
    _=0 := by rw [q1_q0,mul_zero,zero_mul]
 theorem s0_t0_add_s1_t1 : s0 k*t0 k+s1 k*t1 k=q k := by rw [s0_t0,s1_t1,q0_add_q1]

end FiniteAlgebraicEnvelopes.PartialAffine.Corner

section
namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]

def cornerTensor : B →ₙₐ[k] B ⊗[k] MonoidAlgebra k monoid where
  toFun x := x ⊗ₜ[k] q k
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' x y := TensorProduct.add_tmul _ _ _
  map_mul' x y := by rw [Algebra.TensorProduct.tmul_mul_tmul,q_idem]
  map_smul' r x := TensorProduct.smul_tmul' _ _ _

def coefficient0 : MonoidAlgebra k monoid →ₗ[k] k where
  toFun f := f.coeff E0
  map_add' f g := by simp
  map_smul' r f := by simp

 theorem coefficient0_q : coefficient0 k (q k)=1 := by
  change (q k).coeff E0 = 1
  simp [q,b,E0_ne_E1]

def cornerRetract : B ⊗[k] MonoidAlgebra k monoid →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap.comp (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k))

 theorem cornerRetract_cornerTensor (x : B) : cornerRetract k B (cornerTensor k B x)=x := by
  change TensorProduct.rid k B (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k) (x ⊗ₜ[k] q k))=x
  rw [TensorProduct.map_tmul,coefficient0_q]
  simp

 theorem cornerTensor_injective : Function.Injective (cornerTensor k B) :=
  Function.LeftInverse.injective (cornerRetract_cornerTensor k B)
end FiniteAlgebraicEnvelopes.PartialAffine.Corner

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

/-- The actual unital tensor embedding from the algebra construction, not supplied as a hypothesis. -/
def rho : BigAlgebra s h k ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₐ[k] SmallAlgebra s h k :=
  (kappaAlgebra s h k).comp (ZeroProduct.tensorMap k (K s h) PartialAffine.monoid)

theorem rho_injective : Function.Injective (rho s h k) :=
  (kappaAlgebra_injective s h k).comp (ZeroProduct.tensorMap_bijective k (K s h) PartialAffine.monoid).1

def j : BigAlgebra s h k →ₙₐ[k] SmallAlgebra s h k :=
  (rho s h k).toNonUnitalAlgHom.comp (PartialAffine.Corner.cornerTensor k (BigAlgebra s h k))

theorem j_injective : Function.Injective (j s h k) :=
  (rho_injective s h k).comp (PartialAffine.Corner.cornerTensor_injective k (BigAlgebra s h k))

def phi : BigAlgebra s h k →ₙₐ[k] BigAlgebra s h k :=
  (algebraEmbedding s h k).comp (j s h k)

theorem phi_injective [Nontrivial k] : Function.Injective (phi s h k) :=
  (algebraEmbedding_injective s h k).comp (j_injective s h k)

 theorem phi_one_ne_one [Nontrivial k] : phi s h k 1≠1 := by
  intro he
  exact one_not_in_smallAlgebra s h k ⟨j s h k 1,he⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k A B C D : Type*} [CommRing k] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]

def map (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) : A⊗[k] C →ₙₐ[k] B⊗[k] D where
  toFun := TensorProduct.map (f : A →ₗ[k] B) (g : C →ₗ[k] D)
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [add_mul,map_add,hx,hz]
    | tmul a c =>
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [mul_add,map_add,hx,hy]
      | tmul b d => simp only [Algebra.TensorProduct.tmul_mul_tmul,TensorProduct.map_tmul,LinearMap.coe_ofClass,map_mul]

@[simp] theorem map_tmul (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) (a : A) (c : C) :
    map f g (a⊗ₜ[k] c)=f a⊗ₜ[k] g c := TensorProduct.map_tmul _ _ _ _

theorem map_injective [Module.Flat k B] [Module.Flat k C]
    (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map f g) :=
  TensorProduct.map_injective_of_flat_flat (f : A →ₗ[k] B) (g : C →ₗ[k] D) hf hg

def op (f : A →ₙₐ[k] B) : Aᵐᵒᵖ →ₙₐ[k] Bᵐᵒᵖ where
  toFun x := MulOpposite.op (f x.unop)
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp
  map_smul' r x := by simp

@[simp] theorem op_apply (f : A →ₙₐ[k] B) (x : Aᵐᵒᵖ) : op f x=MulOpposite.op (f x.unop) := rfl

theorem op_injective (f : A →ₙₐ[k] B) (hf : Function.Injective f) : Function.Injective (op f) := by
  intro x y he
  exact MulOpposite.unop_injective (hf (MulOpposite.op_injective he))

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open scoped TensorProduct
open PartialAffine.Corner
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

def xi : BigAlgebra s h k ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₙₐ[k] BigAlgebra s h k :=
  (algebraEmbedding s h k).comp (rho s h k).toNonUnitalAlgHom

 theorem phi_eq (a : BigAlgebra s h k) : phi s h k a=xi s h k (a⊗ₜ[k] q k) := rfl

 theorem xi_constant_commute (c : MonoidAlgebra k PartialAffine.monoid)
    (hqc : q k*c=c) (hcq : c*q k=c) (a : BigAlgebra s h k) :
    Commute (xi s h k (1⊗ₜ[k] c)) (phi s h k a) := by
  change xi s h k (1⊗ₜ[k] c)*phi s h k a=phi s h k a*xi s h k (1⊗ₜ[k] c)
  rw [phi_eq,←map_mul,←map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hqc,hcq]

def supported (c d : MonoidAlgebra k PartialAffine.monoid)
    (hdc : d*c=q k) (hqc : q k*c=c) (hcq : c*q k=c) (hqd : q k*d=d) (hdq : d*q k=d) :
    Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) where
  U := xi s h k (1⊗ₜ[k] c)
  V := xi s h k (1⊗ₜ[k] d)
  VU := by
    change xi s h k (1⊗ₜ[k] (d))*xi s h k (1⊗ₜ[k] (c))=xi s h k (1⊗ₜ[k] (q k))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hdc]
  PU := by
    change xi s h k (1⊗ₜ[k] (q k))*xi s h k (1⊗ₜ[k] (c))=xi s h k (1⊗ₜ[k] (c))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hqc]
  UP := by
    change xi s h k (1⊗ₜ[k] (c))*xi s h k (1⊗ₜ[k] (q k))=xi s h k (1⊗ₜ[k] (c))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hcq]
  PV := by
    change xi s h k (1⊗ₜ[k] (q k))*xi s h k (1⊗ₜ[k] (d))=xi s h k (1⊗ₜ[k] (d))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hqd]
  VP := by
    change xi s h k (1⊗ₜ[k] (d))*xi s h k (1⊗ₜ[k] (q k))=xi s h k (1⊗ₜ[k] (d))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hdq]
  commU := xi_constant_commute s h k c hqc hcq
  commV := xi_constant_commute s h k d hqd hdq

def pair0 : Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) :=
  supported s h k (s0 k) (t0 k) (t0_s0 k) (q_s0 k) (s0_q k) (q_t0 k) (t0_q k)
def pair1 : Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) :=
  supported s h k (s1 k) (t1 k) (t1_s1 k) (q_s1 k) (s1_q k) (q_t1 k) (t1_q k)

theorem pair0_pair1 : (pair0 s h k).V*(pair1 s h k).U=0 := by
  change xi s h k (1⊗ₜ[k] t0 k)*xi s h k (1⊗ₜ[k] s1 k)=0
  rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,t0_s1,TensorProduct.tmul_zero,map_zero]
theorem pair1_pair0 : (pair1 s h k).V*(pair0 s h k).U=0 := by
  change xi s h k (1⊗ₜ[k] t1 k)*xi s h k (1⊗ₜ[k] s0 k)=0
  rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,t1_s0,TensorProduct.tmul_zero,map_zero]

theorem pairs_sum : (pair0 s h k).U*(pair0 s h k).V+(pair1 s h k).U*(pair1 s h k).V=phi s h k 1 := by
  change xi s h k (1⊗ₜ[k] s0 k)*xi s h k (1⊗ₜ[k] t0 k)+
    xi s h k (1⊗ₜ[k] s1 k)*xi s h k (1⊗ₜ[k] t1 k)=_
  rw [←map_mul,←map_mul,←map_add,phi_eq]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,←TensorProduct.tmul_add,s0_t0_add_s1_t1]

end

open scoped TensorProduct
open Contracted
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev TAlgebra := Contracted.Algebra k (T s h)

def separatingElement : SmallAlgebra s h k := basis k (H s h) (separator s h) 1

def separationBilinear : TAlgebra s h k →ₗ[k] TAlgebra s h k →ₗ[k] SmallAlgebra s h k :=
  LinearMap.mk₂ k (fun x y => kappaAlgebra s h k x*separatingElement s h k*kappaAlgebra s h k y)
    (by intro a b c; simp [add_mul])
    (by intro r a b; simp [smul_mul_assoc])
    (by intro a b c; simp [mul_add])
    (by intro r a b; simp [mul_smul_comm])

def separationLinear : TAlgebra s h k ⊗[k] TAlgebra s h k →ₗ[k] SmallAlgebra s h k :=
  TensorProduct.lift (separationBilinear s h k)

@[simp] theorem separationLinear_tmul (x y : TAlgebra s h k) :
    separationLinear s h k (x⊗ₜ[k] y)=kappaAlgebra s h k x*separatingElement s h k*kappaAlgebra s h k y := rfl

def separatorIndex (p : {a : T s h // a≠0} × {a : T s h // a≠0}) : {a : H s h // a≠0} :=
  ⟨kappa s h p.1*separator s h*kappa s h p.2,separator_nonzero s h _ _ p.1.property p.2.property⟩

theorem separatorIndex_injective : Function.Injective (separatorIndex s h) := by
  intro a b he
  exact separator_injective s h (congrArg Subtype.val he)

 theorem separationLinear_basis (p : {a : T s h // a≠0} × {a : T s h // a≠0}) :
    separationLinear s h k ((monoidBasis (k:=k) (H:=T s h)).tensorProduct (monoidBasis (k:=k) (H:=T s h)) p)=
      monoidBasis (k:=k) (H:=H s h) (separatorIndex s h p) := by
  rw [Module.Basis.tensorProduct_apply',separationLinear_tmul]
  simp only [monoidBasis_apply,kappaAlgebra,map_basis,separatingElement,basis_mul,one_mul]
  rfl

 theorem separationLinear_injective : Function.Injective (separationLinear s h k) := by
  let b := (monoidBasis (k:=k) (H:=T s h)).tensorProduct (monoidBasis (k:=k) (H:=T s h))
  let v := fun p => monoidBasis (k:=k) (H:=H s h) (separatorIndex s h p)
  have hl : LinearIndependent k v :=
    (monoidBasis (k:=k) (H:=H s h)).linearIndependent.comp (separatorIndex s h) (separatorIndex_injective s h)
  have he : separationLinear s h k=b.constr k v := by
    apply b.ext
    intro p
    rw [Module.Basis.constr_basis]
    exact separationLinear_basis s h k p
  rw [he]
  exact b.injective_constr_of_linearIndependent hl

/-- The map j before the final κ extension, with image in the actual T algebra. -/
def jT : BigAlgebra s h k →ₙₐ[k] TAlgebra s h k :=
  (ZeroProduct.tensorMap k (K s h) PartialAffine.monoid).toNonUnitalAlgHom.comp
    (PartialAffine.Corner.cornerTensor k (BigAlgebra s h k))

theorem jT_injective : Function.Injective (jT s h k) :=
  (ZeroProduct.tensorMap_bijective k (K s h) PartialAffine.monoid).1.comp
    (PartialAffine.Corner.cornerTensor_injective k (BigAlgebra s h k))

 theorem jT_apply (a : BigAlgebra s h k) : kappaAlgebra s h k (jT s h k a)=j s h k a := rfl

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
def linear (f : A →ₙₐ[k] B) : A →ₗ[k] B := f
@[simp] theorem linear_apply (f : A →ₙₐ[k] B) (a : A) : linear f a=f a := rfl
end

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def coefficient (f : A →ₙₐ[k] A) : Enveloping.Coeff k A →ₙₐ[k] Enveloping.Coeff k A := map f (op f)

def ringHom (f : A →ₙₐ[k] A) : A →ₙ+* A := f

@[simp] theorem ringHom_apply (f : A →ₙₐ[k] A) (a : A) : ringHom f a=f a := rfl

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

def act (r : Coeff k A) (a : A) : A := representation k A r a

theorem act_eq_smul (r : Coeff k A) (a : A) : act k A r a=r • a := rfl
@[simp] theorem act_zero (a : A) : act k A 0 a=0 := by simp [act]
theorem act_add (r s : Coeff k A) (a : A) : act k A (r+s) a=act k A r a+act k A s a := by simp [act]
@[simp] theorem act_tmul (a b c : A) : act k A (a⊗ₜ[k] MulOpposite.op b) c=a*c*b := tmul_smul k A a b c
end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def actingLinear (f : A →ₙₐ[k] A) (a : A) : Enveloping.Coeff k A →ₗ[k] A :=
  ((LinearMap.applyₗ (R:=k) (M₂:=A) a).comp (Enveloping.representation k A).toLinearMap).comp (linear (coefficient f))

@[simp] theorem actingLinear_apply (f : A →ₙₐ[k] A) (a : A) (r : Enveloping.Coeff k A) :
    actingLinear f a r=Enveloping.act k A (coefficient f r) a := rfl

@[simp] theorem actingLinear_tmul (f : A →ₙₐ[k] A) (a b c : A) :
    actingLinear f c (a⊗ₜ[k] MulOpposite.op b)=f a*c*f b := Enveloping.act_tmul k A _ _ _
end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev R := Enveloping.Coeff k (BigAlgebra s h k)

local instance sourceModule : Module (R s h k) (BigAlgebra s h k) := Enveloping.module k (BigAlgebra s h k)

def psi := NonunitalTensor.coefficient (phi s h k)

local instance smallFree : Module.Free k (BigAlgebra s h k) := Module.Free.of_basis (Contracted.monoidBasis (k:=k) (H:=K s h))
local instance oppositeFree : Module.Free k (BigAlgebra s h k)ᵐᵒᵖ :=
  Module.Free.of_basis ((Contracted.monoidBasis (k:=k) (H:=K s h)).map (MulOpposite.opLinearEquiv k))
local instance tFree : Module.Free k (TAlgebra s h k) := Module.Free.of_basis (Contracted.monoidBasis (k:=k) (H:=T s h))

theorem psi_injective [Nontrivial k] : Function.Injective (psi s h k) :=
  NonunitalTensor.map_injective _ _ (phi_injective s h k) (NonunitalTensor.op_injective _ (phi_injective s h k))

@[simp] theorem psi_tmul (a b : BigAlgebra s h k) :
    psi s h k (a⊗ₜ[k] MulOpposite.op b)=phi s h k a⊗ₜ[k] MulOpposite.op (phi s h k b) := rfl

def detectionInput : R s h k →ₗ[k] TAlgebra s h k ⊗[k] TAlgebra s h k :=
  TensorProduct.map (NonunitalTensor.linear (jT s h k))
    ((NonunitalTensor.linear (jT s h k)).comp
      (MulOpposite.opLinearEquiv k : BigAlgebra s h k ≃ₗ[k] (BigAlgebra s h k)ᵐᵒᵖ).symm.toLinearMap)

theorem detectionInput_injective : Function.Injective (detectionInput s h k) :=
  TensorProduct.map_injective_of_flat_flat _ _ (jT_injective s h k)
    ((jT_injective s h k).comp MulOpposite.unop_injective)

def detectionLinear : R s h k →ₗ[k] BigAlgebra s h k :=
  (NonunitalTensor.linear (algebraEmbedding s h k)).comp
    ((separationLinear s h k).comp (detectionInput s h k))

theorem detectionLinear_injective [Nontrivial k] : Function.Injective (detectionLinear s h k) :=
  (algebraEmbedding_injective s h k).comp
    ((separationLinear_injective s h k).comp (detectionInput_injective s h k))

def detectingElement : BigAlgebra s h k := algebraEmbedding s h k (separatingElement s h k)

theorem detectionLinear_eq : detectionLinear s h k=NonunitalTensor.actingLinear (phi s h k) (detectingElement s h k) := by
  apply TensorProduct.ext'
  intro a b
  change algebraEmbedding s h k
    (separationLinear s h k (jT s h k a⊗ₜ[k] jT s h k b.unop))=_
  rw [separationLinear_tmul,jT_apply,jT_apply,map_mul,map_mul]
  change phi s h k a*detectingElement s h k*phi s h k b.unop=_
  rw [←MulOpposite.op_unop b,NonunitalTensor.actingLinear_tmul]
  rfl

theorem detectionLinear_apply (r : R s h k) :
    detectionLinear s h k r=Enveloping.act k (BigAlgebra s h k) (psi s h k r) (detectingElement s h k) :=
  DFunLike.congr_fun (detectionLinear_eq s h k) r

/-- The actual separator proves tensor detection, with a single fixed detecting vector. -/
theorem tensor_detection [Nontrivial k] (r : R s h k) (hr : ∀ b : BigAlgebra s h k, Enveloping.act k (BigAlgebra s h k) (psi s h k r) b=0) : r=0 := by
  apply detectionLinear_injective s h k
  calc
    detectionLinear s h k r = Enveloping.act k (BigAlgebra s h k) (psi s h k r) (detectingElement s h k) := detectionLinear_apply s h k r
    _ = 0 := hr _
    _ = detectionLinear s h k 0 := (LinearMap.map_zero _).symm

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open scoped TensorProduct
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable (f : A →ₙₐ[k] A)

def coefficientRing :
    @NonUnitalRingHom (Enveloping.Coeff k A) (Enveloping.Coeff k A)
      (inferInstance : Ring (Enveloping.Coeff k A)).toNonAssocRing.toNonUnitalNonAssocSemiring
      (inferInstance : Ring (Enveloping.Coeff k A)).toNonAssocRing.toNonUnitalNonAssocSemiring :=
  coefficient f

 theorem image_left (a : A) : f 1*f a=f a := by rw [←map_mul,one_mul]
 theorem image_right (a : A) : f a*f 1=f a := by rw [←map_mul,mul_one]
 theorem coefficient_one : coefficient f 1=f 1⊗ₜ[k] MulOpposite.op (f 1) := by
  change coefficient f ((1:A)⊗ₜ[k] (1:(A)ᵐᵒᵖ))=_
  rfl

 theorem tensor_constant_commute (c : A) (hc : ∀ a, Commute c (f a))
    (r : Enveloping.Coeff k A) : Commute (c⊗ₜ[k] MulOpposite.op (f 1)) (coefficient f r) := by
   induction r using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add]; exact ha.add_right hb
  | tmul a b =>
    change (c⊗ₜ[k] MulOpposite.op (f 1))*(f a⊗ₜ[k] MulOpposite.op (f b.unop))=
      (f a⊗ₜ[k] MulOpposite.op (f b.unop))*(c⊗ₜ[k] MulOpposite.op (f 1))
    simp only [Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,image_right,(hc a).eq]

def supportedPair (p : Steinberg.SupportedPair (f : A →ₙ+* A)) :
    Steinberg.SupportedPair (coefficientRing f) where
  U := p.U⊗ₜ[k] MulOpposite.op (f 1)
  V := p.V⊗ₜ[k] MulOpposite.op (f 1)
  VU := by
    change (p.V⊗ₜ[k] MulOpposite.op (f 1))*(p.U⊗ₜ[k] MulOpposite.op (f 1))=coefficient f 1
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,p.VU]
    rfl
  PU := by
    change coefficient f 1*(p.U⊗ₜ[k] MulOpposite.op (f 1))=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change ((f : A →ₙ+* A) 1*p.U)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.PU]
  UP := by
    change (p.U⊗ₜ[k] MulOpposite.op (f 1))*coefficient f 1=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change (p.U*(f : A →ₙ+* A) 1)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.UP]
  PV := by
    change coefficient f 1*(p.V⊗ₜ[k] MulOpposite.op (f 1))=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change ((f : A →ₙ+* A) 1*p.V)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.PV]
  VP := by
    change (p.V⊗ₜ[k] MulOpposite.op (f 1))*coefficient f 1=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change (p.V*(f : A →ₙ+* A) 1)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.VP]
  commU := tensor_constant_commute f p.U (by intro a; exact p.commU a)
  commV := tensor_constant_commute f p.V (by intro a; exact p.commV a)

theorem supportedPair_cross (p q : Steinberg.SupportedPair (f : A →ₙ+* A)) (hpq : p.V*q.U=0) :
    (supportedPair f p).V*(supportedPair f q).U=0 := by
  change (p.V⊗ₜ[k] MulOpposite.op (f 1))*(q.U⊗ₜ[k] MulOpposite.op (f 1))=0
  rw [Algebra.TensorProduct.tmul_mul_tmul,hpq,TensorProduct.zero_tmul]

theorem supportedPair_sum (p q : Steinberg.SupportedPair (f : A →ₙ+* A)) (hpq : p.U*p.V+q.U*q.V=f 1) :
    (supportedPair f p).U*(supportedPair f p).V+(supportedPair f q).U*(supportedPair f q).V=coefficient f 1 := by
  change (p.U⊗ₜ[k] MulOpposite.op (f 1))*(p.V⊗ₜ[k] MulOpposite.op (f 1))+
    (q.U⊗ₜ[k] MulOpposite.op (f 1))*(q.V⊗ₜ[k] MulOpposite.op (f 1))=_
  simp only [Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,←TensorProduct.add_tmul,hpq,coefficient_one]

end

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable (f : A →ₙₐ[k] A)

theorem annihilation (p q : Steinberg.SupportedPair (f : A →ₙ+* A))
    (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=f 1)
    (z : Steinberg.Group (Fin 6) (Enveloping.Coeff k A)) (hz : Steinberg.matrixMap z=1) :
    Steinberg.coefficientMap (coefficientRing f) z=1 :=
  (supportedPair f p).annihilation (supportedPair f q) (supportedPair_cross f p q hpq)
    (supportedPair_cross f q p hqp) (supportedPair_sum f p q hsum) hz

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

local instance : NonUnitalNonAssocSemiring (R s h k) :=
  (inferInstance : Ring (R s h k)).toNonAssocRing.toNonUnitalNonAssocSemiring
local instance : Mul (R s h k) := (inferInstance : Ring (R s h k)).toMul
local instance : Add (R s h k) := (inferInstance : Ring (R s h k)).toAdd
local instance : Zero (R s h k) := (inferInstance : Ring (R s h k)).toZero
local instance : One (R s h k) := (inferInstance : Ring (R s h k)).toOne

def ringPsi : R s h k →ₙ+* R s h k := NonunitalTensor.coefficientRing (phi s h k)

def ringPair0 : Steinberg.SupportedPair (ringPsi s h k) :=
  NonunitalTensor.supportedPair (phi s h k) (pair0 s h k)
def ringPair1 : Steinberg.SupportedPair (ringPsi s h k) :=
  NonunitalTensor.supportedPair (phi s h k) (pair1 s h k)

theorem ringPair01 : (ringPair0 s h k).V * (ringPair1 s h k).U = 0 :=
  NonunitalTensor.supportedPair_cross (phi s h k) (pair0 s h k) (pair1 s h k) (pair0_pair1 s h k)
theorem ringPair10 : (ringPair1 s h k).V * (ringPair0 s h k).U = 0 :=
  NonunitalTensor.supportedPair_cross (phi s h k) (pair1 s h k) (pair0 s h k) (pair1_pair0 s h k)
theorem ringPairSum :
    (ringPair0 s h k).U * (ringPair0 s h k).V +
      (ringPair1 s h k).U * (ringPair1 s h k).V = ringPsi s h k 1 :=
  NonunitalTensor.supportedPair_sum (phi s h k) (pair0 s h k) (pair1 s h k) (pairs_sum s h k)

/-- Actual coefficient endomorphism kills the whole Steinberg kernel in one step. -/
theorem source_kernel_annihilation
    (kernelElement : Steinberg.Group (Fin 6) (R s h k))
    (inKernel : Steinberg.matrixMap kernelElement = 1) :
    Steinberg.coefficientMap (ringPsi s h k) kernelElement = 1 :=
  NonunitalTensor.annihilation (phi s h k) (pair0 s h k) (pair1 s h k)
    (pair0_pair1 s h k) (pair1_pair0 s h k) (pairs_sum s h k) kernelElement inKernel

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
