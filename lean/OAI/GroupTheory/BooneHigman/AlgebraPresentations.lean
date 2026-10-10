import OAI.GroupTheory.BooneHigman.SteinbergLimits

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.TensorPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] (A C : Type*)

abbrev F := FreeAlgebra k (A⊕C)
def inLeft : FreeAlgebra k A →ₐ[k] F k A C := FreeAlgebra.lift k (fun a => FreeAlgebra.ι k (Sum.inl a))
def inRight : FreeAlgebra k C →ₐ[k] F k A C := FreeAlgebra.lift k (fun c => FreeAlgebra.ι k (Sum.inr c))

variable {A C}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop) (s : FreeAlgebra k C → FreeAlgebra k C → Prop)

inductive Rel : F k A C → F k A C → Prop
  | left {a b} : r a b → Rel (inLeft k A C a) (inLeft k A C b)
  | right {a b} : s a b → Rel (inRight k A C a) (inRight k A C b)
  | commute (a : A) (c : C) : Rel (FreeAlgebra.ι k (Sum.inl a)*FreeAlgebra.ι k (Sum.inr c))
      (FreeAlgebra.ι k (Sum.inr c)*FreeAlgebra.ι k (Sum.inl a))

abbrev P := RingQuot (Rel k r s)
def q : F k A C →ₐ[k] P k r s := RingQuot.mkAlgHom k (Rel k r s)

def leftFree : FreeAlgebra k A →ₐ[k] P k r s := (q k r s).comp (inLeft k A C)
def rightFree : FreeAlgebra k C →ₐ[k] P k r s := (q k r s).comp (inRight k A C)

def left : RingQuot r →ₐ[k] P k r s := RingQuot.liftAlgHom k ⟨leftFree k r s,by
  intro a b hab
  exact RingQuot.mkAlgHom_rel k (Rel.left hab)⟩
def right : RingQuot s →ₐ[k] P k r s := RingQuot.liftAlgHom k ⟨rightFree k r s,by
  intro a b hab
  exact RingQuot.mkAlgHom_rel k (Rel.right hab)⟩

@[simp] theorem left_mk (a : FreeAlgebra k A) : left k r s (RingQuot.mkAlgHom k r a)=leftFree k r s a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
@[simp] theorem right_mk (c : FreeAlgebra k C) : right k r s (RingQuot.mkAlgHom k s c)=rightFree k r s c :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem leftFree_ι (a : A) : leftFree k r s (FreeAlgebra.ι k a)=q k r s (FreeAlgebra.ι k (Sum.inl a)) := by
  simp [leftFree,inLeft]
@[simp] theorem rightFree_ι (c : C) : rightFree k r s (FreeAlgebra.ι k c)=q k r s (FreeAlgebra.ι k (Sum.inr c)) := by
  simp [rightFree,inRight]

theorem free_commute (a : FreeAlgebra k A) (c : FreeAlgebra k C) : Commute (leftFree k r s a) (rightFree k r s c) := by
  induction a using FreeAlgebra.induction with
  | grade0 z => rw [AlgHom.commutes]; exact Algebra.commutes _ _
  | grade1 a =>
    induction c using FreeAlgebra.induction with
    | grade0 z => rw [AlgHom.commutes]; exact (Algebra.commutes _ _).symm
    | grade1 c =>
      rw [leftFree_ι,rightFree_ι]
      change q k r s _ * q k r s _=q k r s _ * q k r s _
      rw [←map_mul,←map_mul]
      exact RingQuot.mkAlgHom_rel k (Rel.commute a c)
    | add a b ha hb => rw [map_add]; exact ha.add_right hb
    | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb

theorem quotient_commute (a : RingQuot r) (c : RingQuot s) : Commute (left k r s a) (right k r s c) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  obtain ⟨c,rfl⟩ := RingQuot.mkAlgHom_surjective k s c
  rw [left_mk,right_mk]
  exact free_commute k r s a c

def fromTensor : (RingQuot r ⊗[k] RingQuot s) →ₐ[k] P k r s :=
  Algebra.TensorProduct.lift (left k r s) (right k r s) (quotient_commute k r s)

def toTensorFree : F k A C →ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  FreeAlgebra.lift k (Sum.elim
    (fun a => RingQuot.mkAlgHom k r (FreeAlgebra.ι k a) ⊗ₜ[k] (1:RingQuot s))
    (fun c => (1:RingQuot r) ⊗ₜ[k] RingQuot.mkAlgHom k s (FreeAlgebra.ι k c)))

theorem toTensorFree_left : (toTensorFree k r s).comp (inLeft k A C)=
    Algebra.TensorProduct.includeLeft.comp (RingQuot.mkAlgHom k r) := by
  apply FreeAlgebra.hom_ext
  funext a
  simp [toTensorFree,inLeft]

theorem toTensorFree_right : (toTensorFree k r s).comp (inRight k A C)=
    Algebra.TensorProduct.includeRight.comp (RingQuot.mkAlgHom k s) := by
  apply FreeAlgebra.hom_ext
  funext c
  simp [toTensorFree,inRight]

def toTensor : P k r s →ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  RingQuot.liftAlgHom k ⟨toTensorFree k r s,by
    intro a b hab
    cases hab with
    | left hab =>
      change ((toTensorFree k r s).comp (inLeft k A C)) _ = ((toTensorFree k r s).comp (inLeft k A C)) _
      rw [toTensorFree_left]
      exact congrArg (Algebra.TensorProduct.includeLeft : RingQuot r →ₐ[k] (RingQuot r ⊗[k] RingQuot s)) (RingQuot.mkAlgHom_rel k hab)
    | right hab =>
      change ((toTensorFree k r s).comp (inRight k A C)) _ = ((toTensorFree k r s).comp (inRight k A C)) _
      rw [toTensorFree_right]
      exact congrArg (Algebra.TensorProduct.includeRight : RingQuot s →ₐ[k] (RingQuot r ⊗[k] RingQuot s)) (RingQuot.mkAlgHom_rel k hab)
    | commute a c => simp [toTensorFree,Algebra.TensorProduct.tmul_mul_tmul]⟩

@[simp] theorem toTensor_q (a : F k A C) : toTensor k r s (q k r s a)=toTensorFree k r s a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem toTensor_left (a : RingQuot r) : toTensor k r s (left k r s a)=a ⊗ₜ[k] (1:RingQuot s) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  rw [left_mk]
  change toTensor k r s (q k r s (inLeft k A C a))=_
  rw [toTensor_q]
  exact DFunLike.congr_fun (toTensorFree_left k r s) a

@[simp] theorem toTensor_right (c : RingQuot s) : toTensor k r s (right k r s c)=(1:RingQuot r) ⊗ₜ[k] c := by
  obtain ⟨c,rfl⟩ := RingQuot.mkAlgHom_surjective k s c
  rw [right_mk]
  change toTensor k r s (q k r s (inRight k A C c))=_
  rw [toTensor_q]
  exact DFunLike.congr_fun (toTensorFree_right k r s) c

theorem to_from : (toTensor k r s).comp (fromTensor k r s)=AlgHom.id k _ := by
  apply Algebra.TensorProduct.ext'
  intro a c
  simp [fromTensor]

theorem from_to : (fromTensor k r s).comp (toTensor k r s)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext a
  cases a with
  | inl a =>
    change fromTensor k r s (toTensor k r s (q k r s (FreeAlgebra.ι k (Sum.inl a))))=_
    rw [toTensor_q]
    simp [toTensorFree,fromTensor,q]
  | inr c =>
    change fromTensor k r s (toTensor k r s (q k r s (FreeAlgebra.ι k (Sum.inr c))))=_
    rw [toTensor_q]
    simp [toTensorFree,fromTensor,q]

def equivalence : P k r s ≃ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  AlgEquiv.ofAlgHom (toTensor k r s) (fromTensor k r s) (to_from k r s) (from_to k r s)

theorem rel_finite [Finite A] [Finite C]
    (hr : {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}.Finite)
    (hs : {p : FreeAlgebra k C × FreeAlgebra k C | s p.1 p.2}.Finite) :
    {p : F k A C × F k A C | Rel k r s p.1 p.2}.Finite := by
  let L := (fun p => (inLeft k A C p.1,inLeft k A C p.2)) '' {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}
  let R := (fun p => (inRight k A C p.1,inRight k A C p.2)) '' {p : FreeAlgebra k C × FreeAlgebra k C | s p.1 p.2}
  let T := Set.range (fun p : A×C => (FreeAlgebra.ι k (Sum.inl p.1)*FreeAlgebra.ι k (Sum.inr p.2),
    FreeAlgebra.ι k (Sum.inr p.2)*FreeAlgebra.ι k (Sum.inl p.1)))
  apply (((hr.image _).union (hs.image _)).union (Set.finite_range _)).subset (s:= L ∪ R ∪ T)
  rintro ⟨a,b⟩ hp
  cases hp with
  | left hab => exact Or.inl (Or.inl ⟨(_, _),hab,rfl⟩)
  | right hab => exact Or.inl (Or.inr ⟨(_, _),hab,rfl⟩)
  | commute a c => exact Or.inr ⟨(a,c),rfl⟩

end FiniteAlgebraicEnvelopes.TensorPresentation

namespace FiniteAlgebraicEnvelopes.OppositePresentation
open MulOpposite
variable (k : Type*) [CommRing k] (A : Type*)

def reverse : FreeAlgebra k A →ₐ[k] (FreeAlgebra k A)ᵐᵒᵖ :=
  FreeAlgebra.lift k (fun a => op (FreeAlgebra.ι k a))

def unreverse : (FreeAlgebra k A)ᵐᵒᵖ →ₐ[k] FreeAlgebra k A := AlgHom.opComm (reverse k A)

@[simp] theorem reverse_ι (a : A) : reverse k A (FreeAlgebra.ι k a)=op (FreeAlgebra.ι k a) := by
  simp [reverse]
@[simp] theorem unreverse_op (a : FreeAlgebra k A) : unreverse k A (op a)=(reverse k A a).unop := rfl

theorem unreverse_reverse : (unreverse k A).comp (reverse k A)=AlgHom.id k _ := by
  apply FreeAlgebra.hom_ext
  funext a
  simp

theorem reverse_unreverse : (reverse k A).comp (unreverse k A)=AlgHom.id k _ := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := op_surjective a
  apply unop_injective
  exact DFunLike.congr_fun (unreverse_reverse k A) a

def freeEquivalence : FreeAlgebra k A ≃ₐ[k] (FreeAlgebra k A)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverse k A) (unreverse k A) (reverse_unreverse k A) (unreverse_reverse k A)

variable {A}
variable {R : Type*} [Ring R] [Algebra k R] (r : R → R → Prop)

def opRel (a b : Rᵐᵒᵖ) : Prop := r a.unop b.unop

def quotientToOp : RingQuot (opRel r) →ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k r).op,by
    intro a b hab
    exact congrArg op (RingQuot.mkAlgHom_rel k hab)⟩

def quotientFromOpAux : RingQuot r →ₐ[k] (RingQuot (opRel r))ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k (opRel r)).op.comp (AlgEquiv.opOp k R).toAlgHom,by
    intro a b hab
    exact congrArg op (RingQuot.mkAlgHom_rel k (show opRel r (op a) (op b) from hab))⟩

def quotientFromOp : (RingQuot r)ᵐᵒᵖ →ₐ[k] RingQuot (opRel r) :=
  AlgHom.opComm (quotientFromOpAux k r)

@[simp] theorem quotientToOp_mk (a : Rᵐᵒᵖ) :
    quotientToOp k r (RingQuot.mkAlgHom k (opRel r) a)=op (RingQuot.mkAlgHom k r a.unop) := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
@[simp] theorem quotientFromOp_mk (a : R) :
    quotientFromOp k r (op (RingQuot.mkAlgHom k r a))=RingQuot.mkAlgHom k (opRel r) (op a) := by
  change (quotientFromOpAux k r (RingQuot.mkAlgHom k r a)).unop=_
  congr 1
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem quotientToFrom : (quotientToOp k r).comp (quotientFromOp k r)=AlgHom.id k _ := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := op_surjective a
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  simp

theorem quotientFromTo : (quotientFromOp k r).comp (quotientToOp k r)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply AlgHom.ext
  intro a
  simp

def quotientEquivalence : RingQuot (opRel r) ≃ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (quotientToOp k r) (quotientFromOp k r) (quotientToFrom k r) (quotientFromTo k r)

omit [Ring R] [Algebra k R] in
theorem opRel_finite (hr : {p : R×R | r p.1 p.2}.Finite) :
    {p : Rᵐᵒᵖ×Rᵐᵒᵖ | opRel r p.1 p.2}.Finite := by
  apply (hr.image (fun p => (op p.1,op p.2))).subset
  rintro ⟨a,b⟩ h
  exact ⟨(a.unop,b.unop),h,rfl⟩

variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

def freeRel (a b : FreeAlgebra k A) := opRel r ((freeEquivalence k A) a) ((freeEquivalence k A) b)

def presentation : RingQuot (freeRel k r) ≃ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  (RingQuot.algEquivQuotAlgEquiv (freeEquivalence k A).symm (opRel r)).symm.trans (quotientEquivalence k r)

theorem freeRel_finite (hr : {p : FreeAlgebra k A×FreeAlgebra k A | r p.1 p.2}.Finite) :
    {p : FreeAlgebra k A×FreeAlgebra k A | freeRel k r p.1 p.2}.Finite := by
  apply ((opRel_finite r hr).image (fun p => ((freeEquivalence k A).symm p.1,(freeEquivalence k A).symm p.2))).subset
  rintro ⟨a,b⟩ h
  refine ⟨((freeEquivalence k A) a,(freeEquivalence k A) b),h,?_⟩
  simp

end FiniteAlgebraicEnvelopes.OppositePresentation

namespace FiniteAlgebraicEnvelopes.AlgebraGenerators

section
open scoped TensorProduct
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def tensorGenerators (S : Set A) (T : Set B) : Set (A ⊗[k] B) :=
  ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) '' S) ∪ ((Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) '' T)

theorem tensorGenerators_finite {S : Set A} {T : Set B} (hS : S.Finite) (hT : T.Finite) :
    (tensorGenerators (k:=k) S T).Finite := (hS.image _).union (hT.image _)

theorem tensorGenerators_generate {S : Set A} {T : Set B}
    (hS : Algebra.adjoin k S=⊤) (hT : Algebra.adjoin k T=⊤) :
    Algebra.adjoin k (tensorGenerators (k:=k) S T)=⊤ := by
  let C := Algebra.adjoin k (tensorGenerators (k:=k) S T)
  have hl : ∀ a : A, Algebra.TensorProduct.includeLeft (R:=k) (S:=k) (A:=A) (B:=B) a∈C := by
    have hp : Algebra.adjoin k S≤C.comap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) :=
      Algebra.adjoin_le (fun a ha => Algebra.subset_adjoin (Or.inl ⟨a,ha,rfl⟩))
    rw [hS] at hp
    intro a
    exact hp (by trivial)
  have hr : ∀ b : B, Algebra.TensorProduct.includeRight (R:=k) (A:=A) (B:=B) b∈C := by
    have hp : Algebra.adjoin k T≤C.comap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) :=
      Algebra.adjoin_le (fun b hb => Algebra.subset_adjoin (Or.inr ⟨b,hb,rfl⟩))
    rw [hT] at hp
    intro b
    exact hp (by trivial)
  apply top_unique
  intro x _
  change x∈C
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    have he : a⊗ₜ[k] b=(Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) a*(Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) b := by
      change a⊗ₜ[k] b=(a⊗ₜ[k] (1:B))*((1:A)⊗ₜ[k] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rw [he]
    exact C.mul_mem (hl a) (hr b)
  | add a b ha hb => exact C.add_mem (ha (by trivial)) (hb (by trivial))

theorem oppositeGenerators_generate {S : Set A} (hS : Algebra.adjoin k S=⊤) :
    Algebra.adjoin k (MulOpposite.op '' S)=⊤ := by
  have hset : MulOpposite.op '' S=MulOpposite.unop ⁻¹' S := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩; exact hb
    · intro ha; exact ⟨a.unop,ha,MulOpposite.op_unop a⟩
  rw [hset,←Subalgebra.op_adjoin,hS]
  exact Subalgebra.op_top

end

open scoped TensorProduct
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

def envelopingGenerators (S : Set B) : Set (Enveloping.Coeff (ZMod 2) B) :=
  tensorGenerators (k:=ZMod 2) S (MulOpposite.op '' S)

theorem envelopingGenerators_finite {S : Set B} (hS : S.Finite) :
    (envelopingGenerators S).Finite := tensorGenerators_finite hS (hS.image _)

theorem envelopingGenerators_generate {S : Set B} (hS : Algebra.adjoin (ZMod 2) S=⊤) :
    Subring.closure (envelopingGenerators S)=⊤ :=
  Steinberg.ringGenerators_of_algebraGenerators (R:=Enveloping.Coeff (ZMod 2) B)
    (tensorGenerators_generate (k:=ZMod 2) hS (oppositeGenerators_generate (k:=ZMod 2) hS))

end FiniteAlgebraicEnvelopes.AlgebraGenerators

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (f : B →ₙₐ[k] B) (p q : Steinberg.SupportedPair (f : B →ₙ+* B))
variable (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=f 1)

def linearLimitEquivalence := Steinberg.limitEquivalence (R:=Enveloping.Coeff k B)
  (coefficientRing f) (annihilation f p q hpq hqp hsum)

end FiniteAlgebraicEnvelopes.NonunitalTensor

section
namespace FiniteAlgebraicEnvelopes.ContractedPresentation
variable {k M : Type*} [CommRing k] [Nontrivial k] [MonoidWithZero M]

theorem monoidBasis_injective_nonzero {x y : M} (hx : x≠0)
    (he : monoidBasis k x=monoidBasis k y) : x=y := by
  classical
  have hh := congrArg (Contracted.coefficient (k:=k) x hx) he
  change Contracted.coefficient x hx (Contracted.basis k M x 1)=Contracted.coefficient x hx (Contracted.basis k M y 1) at hh
  rw [Contracted.coefficient_basis,Contracted.coefficient_basis] at hh
  by_contra hn
  simp [hn] at hh
end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

/-- Input units in the simple algebra, whose internal identity is preserved. -/
def groupAlgebraEmbedding : G →* SmallAlgebra s h k :=
  (ContractedPresentation.monoidBasis k).comp (groupEmbedding s h hs)

theorem groupAlgebraEmbedding_injective : Function.Injective (groupAlgebraEmbedding s h k hs) := by
  intro x y he
  apply groupEmbedding_injective s h hs
  exact ContractedPresentation.monoidBasis_injective_nonzero
    (Units.ne_zero (groupUnitsEmbedding s h hs x)) he

def groupAlgebraUnits : G →* (SmallAlgebra s h k)ˣ := (groupAlgebraEmbedding s h k hs).toHomUnits

theorem groupAlgebraUnits_injective : Function.Injective (groupAlgebraUnits s h k hs) := by
  intro x y he
  exact groupAlgebraEmbedding_injective s h k hs (congrArg Units.val he)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Unitize
variable {A B G : Type*} [Ring A] [Ring B] [Group G]
variable (i : A →ₙ+* B) (f : G →* A)

 theorem support_left (a : A) : i 1*i a=i a := by rw [←map_mul,one_mul]
 theorem support_right (a : A) : i a*i 1=i a := by rw [←map_mul,mul_one]

/-- Extend a group represented in a nonunital corner to units of the ambient ring. -/
def hom : G →* B where
  toFun g := 1-i 1+i (f g)
  map_one' := by rw [f.map_one,sub_add_cancel]
  map_mul' g h := by
    rw [map_mul,map_mul]
    have he : i 1*i 1=i 1 := support_left i 1
    have hg := support_right i (f g)
    have hh := support_left i (f h)
    noncomm_ring [he,hg,hh]

@[simp] theorem hom_apply (g : G) : hom i f g=1-i 1+i (f g) := rfl

theorem hom_injective (hi : Function.Injective i) (hf : Function.Injective f) : Function.Injective (hom i f) := by
  intro x y he
  exact hf (hi (add_left_cancel he))

def unitsHom : G →* Bˣ := (hom i f).toHomUnits

theorem unitsHom_injective (hi : Function.Injective i) (hf : Function.Injective f) : Function.Injective (unitsHom i f) := by
  intro x y he
  exact hom_injective i f hi hf (congrArg Units.val he)

end FiniteAlgebraicEnvelopes.Unitize

namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

def includeLeft : A →ₐ[k] Coeff k A := Algebra.TensorProduct.includeLeft

@[simp] theorem includeLeft_apply (a : A) : includeLeft k A a=a⊗ₜ[k] (1:Aᵐᵒᵖ) := rfl

theorem eval_includeLeft (a : A) : eval k A (includeLeft k A a)=a := by
  rw [includeLeft_apply,←MulOpposite.op_one,eval_tmul,mul_one]

theorem includeLeft_injective : Function.Injective (includeLeft k A) :=
  Function.LeftInverse.injective (eval_includeLeft k A)

def unitsInclude : Aˣ →* (Coeff k A)ˣ := Units.map (includeLeft k A).toMonoidHom

theorem unitsInclude_injective : Function.Injective (unitsInclude k A) := by
  intro x y he
  apply Units.ext
  exact includeLeft_injective k A (congrArg Units.val he)

end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

def ambientUnits : G →* (BigAlgebra s h k)ˣ :=
  Unitize.unitsHom (algebraEmbedding s h k) (groupAlgebraEmbedding s h k hs)

theorem ambientUnits_injective : Function.Injective (ambientUnits s h k hs) :=
  Unitize.unitsHom_injective _ _ (algebraEmbedding_injective s h k) (groupAlgebraEmbedding_injective s h k hs)

def coefficientUnits : G →* (R s h k)ˣ :=
  (Enveloping.unitsInclude k (BigAlgebra s h k)).comp (ambientUnits s h k hs)

theorem coefficientUnits_injective : Function.Injective (coefficientUnits s h k hs) :=
  (Enveloping.unitsInclude_injective k (BigAlgebra s h k)).comp (ambientUnits_injective s h k hs)

end

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

theorem ringPsi_injective : Function.Injective (ringPsi s h k) := psi_injective s h k

def linearTransition := Steinberg.elementaryTransition (R:=R s h k) (ringPsi s h k)

theorem linearTransition_injective : Function.Injective (linearTransition s h k) :=
  Steinberg.elementaryTransition_injective (R:=R s h k) _ (ringPsi_injective s h k)

def linearLimitEquivalence := NonunitalTensor.linearLimitEquivalence (phi s h k) (pair0 s h k) (pair1 s h k)
  (pair0_pair1 s h k) (pair1_pair0 s h k) (pairs_sum s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes

/-- A construction interface; every field is discharged below from the source algebra. -/
def HasKernelRing (H : Type*) [Group H] : Prop :=
  ∃ (R : Type) (_ : Ring R) (ψ : R →ₙ+* R), Function.Injective ψ ∧
    (∀ z : Steinberg.Group (Fin 6) R, Steinberg.matrixMap z=1 → Steinberg.coefficientMap ψ z=1) ∧
    ∃ ν : H →* Rˣ, Function.Injective ν

namespace NonunitalTensor
variable {k B : Type} [CommRing k] [Ring B] [Algebra k B]
variable {H : Type*} [Group H]
variable (f : B →ₙₐ[k] B) (p q : Steinberg.SupportedPair (f : B →ₙ+* B))
variable (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=f 1)

include p q hpq hqp hsum
theorem kernelRingPackage (hf : Function.Injective (coefficientRing f))
    (ν : H →* (Enveloping.Coeff k B)ˣ) (hν : Function.Injective ν) : HasKernelRing H :=
  ⟨Enveloping.Coeff k B,inferInstance,coefficientRing f,hf,annihilation f p q hpq hqp hsum,ν,hν⟩
end NonunitalTensor

namespace Bootstrap.Source
variable {H : Type*} [Group H] {n : ℕ} (s : Fin n → H)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (hs : Subgroup.closure (Set.range s)=⊤)

include s h hs
theorem kernelRing : HasKernelRing H :=
  NonunitalTensor.kernelRingPackage (phi s h (ZMod 2)) (pair0 s h (ZMod 2)) (pair1 s h (ZMod 2))
    (pair0_pair1 s h (ZMod 2)) (pair1_pair0 s h (ZMod 2)) (pairs_sum s h (ZMod 2))
    (ringPsi_injective s h (ZMod 2)) (coefficientUnits s h (ZMod 2) hs) (coefficientUnits_injective s h (ZMod 2) hs)
end Bootstrap.Source

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

local instance ringRightSMul :
    SMul (BigAlgebra s h (ZMod 2))ᵐᵒᵖ (BigAlgebra s h (ZMod 2)) :=
  Mul.toSMulMulOpposite _

def ringGenerators : Set (R s h (ZMod 2)) :=
  AlgebraGenerators.tensorGenerators (k:=ZMod 2) (bigGenerators s h (ZMod 2))
    (MulOpposite.op '' bigGenerators s h (ZMod 2))

theorem ringGenerators_finite : (ringGenerators s h).Finite :=
  AlgebraGenerators.tensorGenerators_finite (bigGenerators_finite s h (ZMod 2))
    ((bigGenerators_finite s h (ZMod 2)).image _)

theorem ringGenerators_generate : Subring.closure (ringGenerators s h) = ⊤ :=
  AlgebraGenerators.envelopingGenerators_generate (bigGenerators_generate s h (ZMod 2))

instance steinberg_finitelyGenerated : Group.FG (Steinberg.Group (Fin 6) (R s h (ZMod 2))) :=
  Steinberg.finitelyGenerated_of_ringGenerators (ringGenerators_finite s h) (ringGenerators_generate s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.EnvelopingPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] {A : Type*}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

abbrev Generators := A⊕A
def Rel : FreeAlgebra k (Generators (A:=A)) → FreeAlgebra k (Generators (A:=A)) → Prop :=
  TensorPresentation.Rel k r (OppositePresentation.freeRel k r)

def equivalence : RingQuot (Rel k r) ≃ₐ[k] (RingQuot r ⊗[k] (RingQuot r)ᵐᵒᵖ) :=
  (TensorPresentation.equivalence k r (OppositePresentation.freeRel k r)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : RingQuot r ≃ₐ[k] RingQuot r)
      (OppositePresentation.presentation k r))

theorem rel_finite [Finite A]
    (hr : {p : FreeAlgebra k A × FreeAlgebra k A | r p.1 p.2}.Finite) :
    {p : FreeAlgebra k (Generators (A:=A)) × FreeAlgebra k (Generators (A:=A)) |
      Rel k r p.1 p.2}.Finite :=
  TensorPresentation.rel_finite k r (OppositePresentation.freeRel k r) hr
    (OppositePresentation.freeRel_finite k r hr)

variable {B : Type*} [Ring B] [Algebra k B]
def ofPresentation (e : RingQuot r ≃ₐ[k] B) : RingQuot (Rel k r) ≃ₐ[k] Enveloping.Coeff k B :=
  (equivalence k r).trans (Algebra.TensorProduct.congr e e.op)

end FiniteAlgebraicEnvelopes.EnvelopingPresentation

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {ι : Type*} {R S : Type*} [Ring R] [Ring S]

def coefficientEquiv (e : R ≃+* S) : Group ι R ≃* Group ι S :=
  { coefficientMap e.toRingHom.toNonUnitalRingHom with
    invFun := coefficientMap e.symm.toRingHom.toNonUnitalRingHom
    left_inv := by
      have he : (coefficientMap e.symm.toRingHom.toNonUnitalRingHom).comp
          (coefficientMap e.toRingHom.toNonUnitalRingHom)=MonoidHom.id (Group ι R) := by
        apply PresentedGroup.ext
        rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
        change coefficientMap _ (coefficientMap _ (root i j hij a))=root i j hij a
        simp only [coefficientMap_root]
        change root i j hij (e.symm (e a))=root i j hij a
        rw [e.symm_apply_apply]
      exact DFunLike.congr_fun he
    right_inv := by
      have he : (coefficientMap e.toRingHom.toNonUnitalRingHom).comp
          (coefficientMap e.symm.toRingHom.toNonUnitalRingHom)=MonoidHom.id (Group ι S) := by
        apply PresentedGroup.ext
        rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
        change coefficientMap _ (coefficientMap _ (root i j hij a))=root i j hij a
        simp only [coefficientMap_root]
        change root i j hij (e (e.symm a))=root i j hij a
        rw [e.apply_symm_apply]
      exact DFunLike.congr_fun he }

end FiniteAlgebraicEnvelopes.Steinberg

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev CoefficientGenerators := AlgebraGenerators s h ⊕ AlgebraGenerators s h

def CoefficientRelations := EnvelopingPresentation.Rel k (AlgebraRelations s h k)

def coefficientPresentation := EnvelopingPresentation.ofPresentation k (AlgebraRelations s h k)
  (algebraPresentation s h k)

theorem coefficientRelations_finite :
    {pair : FreeAlgebra k (CoefficientGenerators s h) × FreeAlgebra k (CoefficientGenerators s h) |
      CoefficientRelations s h k pair.1 pair.2}.Finite :=
  EnvelopingPresentation.rel_finite k (AlgebraRelations s h k) (algebraRelations_finite s h k)

/-- Finite-presentation reduction to the finite free algebra case. -/

theorem steinberg_finitePresentation_of_free
    [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (FreeAlgebra k (CoefficientGenerators s h)))] :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (R s h k)) := by
  let : Group.IsFinitelyPresented (Steinberg.Group (Fin 6)
      (RingQuot (EnvelopingPresentation.Rel k (AlgebraRelations s h k)))) :=
    Steinberg.ringQuot_finitelyPresented (CoefficientRelations s h k) (coefficientRelations_finite s h k)
  exact Group.IsFinitelyPresented.equiv (Steinberg.coefficientEquiv (coefficientPresentation s h k).toRingEquiv)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
