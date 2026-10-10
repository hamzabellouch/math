import Mathlib

namespace OAI

noncomputable section

/-!
Self-similar binary group categories, associativity, symmetry, naturality, and braids.
-/

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory

section
universe u
open CategoryTheory

/-- Binary self-similarity data for a group, with the associativity laws in
explicit multiplicative orientation. The concrete finite structural quotient
supplies every field; this is not an assumption on the main theorem's input. -/
structure Data (H : Type u) [Group H] where
  tensor : H × H →* H
  a : H
  naturality : ∀ g h k,a * tensor (g,tensor (h,k)) * a⁻¹=tensor (tensor (g,h),k)
  pentagon : a*a=tensor (a,1)*a*tensor (1,a)

inductive Object (H : Type u)
  | zero | positive
  deriving DecidableEq

variable {H : Type u} [Group H]

@[ext] structure Hom (A B : Object H) where
  val : H
  object_eq : A=B
  unit_eq : A=.zero → val=1

namespace Hom
lemma eq_one {A B : Object H} (f : Hom A B) (h : A=.zero) : f.val=1 := f.unit_eq h

def id (A : Object H) : Hom A A := ⟨1,rfl,fun _=>rfl⟩
def comp {A B C : Object H} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.val*f.val,f.object_eq.trans g.object_eq,by
    intro h
    rw [f.unit_eq h,g.unit_eq (f.object_eq.symm.trans h),mul_one]⟩
end Hom

instance : Category (Object H) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext; exact mul_one _
  comp_id f := by apply Hom.ext; exact one_mul _
  assoc f g h := by apply Hom.ext; exact (mul_assoc _ _ _).symm

@[simp] lemma id_val (A : Object H) : (𝟙 A : Hom A A).val=1 := rfl
@[simp] lemma comp_val {A B C : Object H} (f : A ⟶ B) (g : B ⟶ C) :
    (f≫g).val=g.val*f.val := rfl

namespace Object
omit [Group H]
abbrev tensor : Object H → Object H → Object H
  | .zero,B => B
  | .positive,_ => .positive
@[simp] lemma tensor_zero (A : Object H) : tensor A .zero=A := by cases A <;> rfl
@[simp] lemma zero_tensor (A : Object H) : tensor .zero A=A := rfl
@[simp] lemma tensor_assoc (A B C : Object H) : tensor (tensor A B) C=tensor A (tensor B C) := by
  cases A <;> cases B <;> cases C <;> rfl
end Object

variable (d : Data H)

def tensorVal (A B : Object H) (f g : H) : H :=
  match A,B with
  | .zero,_ => g
  | _,.zero => f
  | .positive,.positive => d.tensor (f,g)

@[simp] lemma tensorVal_zero_left (B : Object H) (f g : H) : tensorVal d .zero B f g=g := rfl

def tensorHom {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    Object.tensor A₁ B₁ ⟶ Object.tensor A₂ B₂ :=
  ⟨tensorVal d A₁ B₁ f.val g.val,congrArg₂ Object.tensor f.object_eq g.object_eq,by
    cases A₁ <;> cases B₁
    · intro _; exact g.unit_eq rfl
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h⟩

lemma tensorHom_val {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    (tensorHom d f g).val=tensorVal d A₁ B₁ f.val g.val := rfl

lemma tensor_id (A B : Object H) : tensorHom d (𝟙 A) (𝟙 B)=𝟙 (Object.tensor A B) := by
  apply Hom.ext
  cases A <;> cases B <;> simp only [tensorHom_val,tensorVal,id_val]
  exact d.tensor.map_one

lemma tensor_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Object H}
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    tensorHom d f g ≫ tensorHom d h k=tensorHom d (f≫h) (g≫k) := by
  have ha := f.object_eq; have hb := g.object_eq
  subst A₂; subst B₂
  apply Hom.ext
  cases A₁ <;> cases B₁ <;> simp only [comp_val,tensorHom_val,tensorVal]
  exact (d.tensor.map_mul (h.val,k.val) (f.val,g.val)).symm

def iso {A B : Object H} (h : A=B) (g : H) (hg : A=.zero → g=1) : A ≅ B where
  hom := ⟨g,h,hg⟩
  inv := ⟨g⁻¹,h.symm,by intro hb; rw [hg (h.trans hb),inv_one]⟩
  hom_inv_id := by apply Hom.ext; exact inv_mul_cancel _
  inv_hom_id := by apply Hom.ext; exact mul_inv_cancel _

def associatorVal : Object H → Object H → Object H → H
  | .positive,.positive,.positive => d.a⁻¹
  | _,_,_ => 1

def associator (A B C : Object H) :
    Object.tensor (Object.tensor A B) C ≅ Object.tensor A (Object.tensor B C) :=
  iso (Object.tensor_assoc A B C) (associatorVal d A B C) (by
    intro h; cases A <;> cases B <;> cases C <;> first | rfl | cases h)

def leftUnitor (A : Object H) : Object.tensor .zero A ≅ A := iso rfl 1 (fun _=>rfl)
def rightUnitor (A : Object H) : Object.tensor A .zero ≅ A :=
  iso (Object.tensor_zero A) 1 (fun _=>rfl)

@[instance_reducible] def monoidalStruct : MonoidalCategoryStruct (Object H) where
  tensorObj := Object.tensor
  whiskerLeft A _ _ g := tensorHom d (𝟙 A) g
  whiskerRight f B := tensorHom d f (𝟙 B)
  tensorHom := tensorHom d
  tensorUnit := .zero
  associator := associator d
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

lemma associator_natural {A₁ A₂ B₁ B₂ C₁ C₂ : Object H}
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : C₁ ⟶ C₂) :
    tensorHom d (tensorHom d f g) h ≫ (associator d A₂ B₂ C₂).hom=
      (associator d A₁ B₁ C₁).hom ≫ tensorHom d f (tensorHom d g h) := by
  have ha := f.object_eq; have hb := g.object_eq; have hc := h.object_eq
  subst A₂; subst B₂; subst C₂
  have hf := f.unit_eq; have hg := g.unit_eq; have hh := h.unit_eq
  apply Hom.ext
  change associatorVal d A₁ B₁ C₁ * tensorVal d (Object.tensor A₁ B₁) C₁
      (tensorVal d A₁ B₁ f.val g.val) h.val=
    tensorVal d A₁ (Object.tensor B₁ C₁) f.val (tensorVal d B₁ C₁ g.val h.val) *
      associatorVal d A₁ B₁ C₁
  cases A₁ <;> cases B₁ <;> cases C₁ <;>
    simp_all only [associatorVal,tensorVal,one_mul,mul_one,forall_const]
  rw [← d.naturality f.val g.val h.val]
  group

lemma leftUnitor_natural {A B : Object H} (f : A ⟶ B) :
    tensorHom d (𝟙 (.zero : Object H)) f ≫ (leftUnitor B).hom=(leftUnitor A).hom ≫ f := by
  apply Hom.ext
  simp only [comp_val,tensorHom_val,leftUnitor,iso,tensorVal,one_mul,mul_one]

lemma rightUnitor_natural {A B : Object H} (f : A ⟶ B) :
    tensorHom d f (𝟙 (.zero : Object H)) ≫ (rightUnitor B).hom=(rightUnitor A).hom ≫ f := by
  apply Hom.ext
  cases A
  · simp only [comp_val,tensorHom_val,rightUnitor,iso,tensorVal,id_val,mul_one]
    exact (f.unit_eq rfl).symm
  · simp only [comp_val,tensorHom_val,rightUnitor,iso,tensorVal,one_mul,mul_one]

lemma pentagon (A B C E : Object H) :
    tensorHom d (associator d A B C).hom (𝟙 E) ≫
      (associator d A (Object.tensor B C) E).hom ≫
        tensorHom d (𝟙 A) (associator d B C E).hom =
      (associator d (Object.tensor A B) C E).hom ≫
        (associator d A B (Object.tensor C E)).hom := by
  apply Hom.ext
  change (tensorVal d A (Object.tensor (Object.tensor B C) E) 1 (associatorVal d B C E) *
    associatorVal d A (Object.tensor B C) E) *
      tensorVal d (Object.tensor (Object.tensor A B) C) E (associatorVal d A B C) 1=
    associatorVal d A B (Object.tensor C E) * associatorVal d (Object.tensor A B) C E
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;> cases E <;>
    simp only [associatorVal,tensorVal,hone,one_mul,mul_one]
  have hm := congrArg (fun z : H=>z⁻¹) d.pentagon
  simpa only [mul_inv_rev,← map_inv,Prod.inv_mk,inv_one,mul_assoc] using hm.symm

lemma triangle (A B : Object H) :
    (associator d A .zero B).hom ≫ tensorHom d (𝟙 A) (leftUnitor B).hom=
      tensorHom d (rightUnitor A).hom (𝟙 B) := by
  apply Hom.ext
  change tensorVal d A (Object.tensor .zero B) 1 1 * associatorVal d A .zero B=
    tensorVal d (Object.tensor A .zero) B 1 1
  cases A <;> cases B <;> simp only [associatorVal,tensorVal,mul_one]

@[instance_reducible] def monoidal : MonoidalCategory (Object H) := by
  letI := monoidalStruct d
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id d)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensor_comp d)
    (associator_naturality := associator_natural d)
    (leftUnitor_naturality := leftUnitor_natural d)
    (rightUnitor_naturality := rightUnitor_natural d)
    (pentagon := pentagon d)
    (triangle := triangle d)

end

section
universe u
open CategoryTheory
variable {H : Type u} [Group H] (d : Data H)

structure SymmetryData where
  c : H
  square : c*c=1
  naturality : ∀ g h,c*d.tensor (g,h)*c⁻¹=d.tensor (h,g)
  hexagon : c=d.a*d.tensor (1,c)*d.a⁻¹*d.tensor (c,1)*d.a

variable (q : SymmetryData d)
lemma symmetry_inv : q.c⁻¹=q.c := inv_eq_of_mul_eq_one_right q.square

def braidingVal : Object H → Object H → H
  | .positive,.positive => q.c
  | _,_ => 1

def braiding (A B : Object H) : Object.tensor A B ≅ Object.tensor B A :=
  iso (by cases A <;> cases B <;> rfl) (braidingVal d q A B) (by
    intro h; cases A <;> cases B <;> first | rfl | cases h)

lemma braiding_natural {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    tensorHom d f g ≫ (braiding d q A₂ B₂).hom=
      (braiding d q A₁ B₁).hom ≫ tensorHom d g f := by
  have ha := f.object_eq; have hb := g.object_eq
  subst A₂; subst B₂
  have hf := f.unit_eq; have hg := g.unit_eq
  apply Hom.ext
  change braidingVal d q A₁ B₁ * tensorVal d A₁ B₁ f.val g.val=
    tensorVal d B₁ A₁ g.val f.val * braidingVal d q A₁ B₁
  cases A₁ <;> cases B₁ <;> simp_all only [braidingVal,tensorVal,one_mul,mul_one,forall_const]
  calc
    _=(q.c*d.tensor (f.val,g.val)*q.c⁻¹)*q.c := by group
    _=_ := by rw [q.naturality]

lemma hexagon_equation : d.a⁻¹*q.c*d.a⁻¹=d.tensor (1,q.c)*d.a⁻¹*d.tensor (q.c,1) := by
  conv_lhs => arg 1; arg 2; rw [q.hexagon]
  group

lemma hexagon_equation_reverse : d.a*q.c*d.a=d.tensor (q.c,1)*d.a*d.tensor (1,q.c) := by
  have h := congrArg (fun z : H=>z⁻¹) (hexagon_equation d q)
  simpa only [mul_inv_rev,inv_inv,← map_inv,Prod.inv_mk,inv_one,symmetry_inv,mul_assoc] using h

lemma braiding_hexagon_forward (A B C : Object H) :
    (associator d A B C).hom ≫ (braiding d q A (Object.tensor B C)).hom ≫
      (associator d B C A).hom =
    tensorHom d (braiding d q A B).hom (𝟙 C) ≫ (associator d B A C).hom ≫
      tensorHom d (𝟙 B) (braiding d q A C).hom := by
  apply Hom.ext
  change (associatorVal d B C A * braidingVal d q A (Object.tensor B C)) * associatorVal d A B C=
    (tensorVal d B (Object.tensor A C) 1 (braidingVal d q A C) * associatorVal d B A C) *
      tensorVal d (Object.tensor A B) C (braidingVal d q A B) 1
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;>
    simp only [associatorVal,braidingVal,tensorVal,hone,one_mul,mul_one]
  exact hexagon_equation d q

lemma braiding_hexagon_reverse (A B C : Object H) :
    (associator d A B C).inv ≫ (braiding d q (Object.tensor A B) C).hom ≫
      (associator d C A B).inv =
    tensorHom d (𝟙 A) (braiding d q B C).hom ≫ (associator d A C B).inv ≫
      tensorHom d (braiding d q A C).hom (𝟙 B) := by
  apply Hom.ext
  change ((associatorVal d C A B)⁻¹ * braidingVal d q (Object.tensor A B) C) *
      (associatorVal d A B C)⁻¹=
    (tensorVal d (Object.tensor A C) B (braidingVal d q A C) 1 * (associatorVal d A C B)⁻¹) *
      tensorVal d A (Object.tensor B C) 1 (braidingVal d q B C)
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;>
    simp only [associatorVal,braidingVal,tensorVal,hone,one_mul,mul_one,inv_one,inv_inv]
  exact hexagon_equation_reverse d q

lemma braiding_symmetry (A B : Object H) :
    (braiding d q A B).hom ≫ (braiding d q B A).hom=𝟙 (Object.tensor A B) := by
  apply Hom.ext
  change braidingVal d q B A * braidingVal d q A B=1
  cases A <;> cases B <;> simp only [braidingVal,one_mul]
  exact q.square

@[instance_reducible] def symmetric : letI := monoidal d; SymmetricCategory (Object H) := by
  letI := monoidal d
  exact
    { braiding := braiding d q
      braiding_naturality_right := fun X _ _ f=>braiding_natural d q (𝟙 X) f
      braiding_naturality_left := fun f Z=>braiding_natural d q f (𝟙 Z)
      hexagon_forward := braiding_hexagon_forward d q
      hexagon_reverse := braiding_hexagon_reverse d q
      symmetry := braiding_symmetry d q }

end

section
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma tensor_conjugate (a b g h : H) :
    d.tensor (a*g*a⁻¹,b*h*b⁻¹)=d.tensor (a,b)*d.tensor (g,h)*(d.tensor (a,b))⁻¹ := by
  change d.tensor (((a,b)*(g,h))*(a,b)⁻¹)=_
  rw [map_mul,map_mul,map_inv]

lemma tensor_commute {a b g h : H} (ha : Commute a g) (hb : Commute b h) :
    Commute (d.tensor (a,b)) (d.tensor (g,h)) := by
  apply Commute.map
  change (a*g,b*h)=(g*a,h*b)
  exact Prod.ext ha.eq hb.eq

/-- The four-leaf middle transposition, expressed only in associator, symmetry
and binary tensor; its naturality is needed in the colour-orbit reduction. -/
def middleSwap : H :=
  d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹

lemma middleSwap_naturality (g : H) :
    Commute (middleSwap d q) (d.tensor (d.tensor (g,g),d.tensor (g,g))) := by
  let D := d.tensor (g,g)
  let Q := d.tensor (g,d.tensor (D,g))
  let K := d.a*d.tensor (1,d.a⁻¹)
  let C := d.tensor (1,d.tensor (q.c,1))
  have hc : Commute q.c D := by
    have h := q.naturality g g
    change q.c*D*q.c⁻¹=D at h
    change q.c*D=D*q.c
    calc
      _=(q.c*D*q.c⁻¹)*q.c := by group
      _=_ := by rw [h]
  have hC : Commute C Q :=
    tensor_commute d (Commute.one_left g)
      (tensor_commute d hc (Commute.one_left g))
  have hi : d.a⁻¹*d.tensor (D,g)*d.a=d.tensor (g,D) := by
    have h := d.naturality g g g
    change d.a*d.tensor (g,D)*d.a⁻¹=d.tensor (D,g) at h
    rw [← h]
    group
  have hK : K*Q*K⁻¹=d.tensor (D,D) := by
    calc
      _=d.a*(d.tensor (1,d.a⁻¹)*Q*(d.tensor (1,d.a⁻¹))⁻¹)*d.a⁻¹ := by
        dsimp [K]; group
      _=d.a*d.tensor (g,d.a⁻¹*d.tensor (D,g)*d.a)*d.a⁻¹ := by
        rw [← tensor_conjugate]
        simp only [one_mul,inv_one,mul_one,inv_inv]
      _=d.a*d.tensor (g,d.tensor (g,D))*d.a⁻¹ := by rw [hi]
      _=d.tensor (D,D) := d.naturality g g D
  have hM : middleSwap d q=K*C*K⁻¹ := by
    change d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹=_
    have ht := tensor_conjugate d (1:H) d.a⁻¹ (1:H) (d.tensor (q.c,1))
    simp only [inv_one,mul_one,inv_inv] at ht
    rw [ht]
    dsimp [K,C]
    group
  have hm := hC.map (MulAut.conj K).toMonoidHom
  change Commute (K*C*K⁻¹) (K*Q*K⁻¹) at hm
  rwa [hK,← hM] at hm

lemma reassociate_four (a b c e : H) :
    let K := d.a*d.tensor (1,d.a⁻¹)
    K*d.tensor (a,d.tensor (d.tensor (b,c),e))*K⁻¹=
      d.tensor (d.tensor (a,b),d.tensor (c,e)) := by
  dsimp only
  have hi : d.a⁻¹*d.tensor (d.tensor (b,c),e)*d.a=d.tensor (b,d.tensor (c,e)) := by
    rw [← d.naturality b c e]
    group
  calc
    _=d.a*(d.tensor (1,d.a⁻¹)*d.tensor (a,d.tensor (d.tensor (b,c),e))*
      (d.tensor (1,d.a⁻¹))⁻¹)*d.a⁻¹ := by group
    _=d.a*d.tensor (a,d.a⁻¹*d.tensor (d.tensor (b,c),e)*d.a)*d.a⁻¹ := by
      rw [← tensor_conjugate]
      simp only [one_mul,inv_one,mul_one,inv_inv]
    _=d.a*d.tensor (a,d.tensor (b,d.tensor (c,e)))*d.a⁻¹ := by rw [hi]
    _=_ := d.naturality a b (d.tensor (c,e))

/-- Full four-leaf naturality, not just the identical-label specialization. -/
lemma middleSwap_interchange (a b c e : H) :
    middleSwap d q*d.tensor (d.tensor (a,b),d.tensor (c,e))*(middleSwap d q)⁻¹=
      d.tensor (d.tensor (a,c),d.tensor (b,e)) := by
  let K := d.a*d.tensor (1,d.a⁻¹)
  let C := d.tensor (1,d.tensor (q.c,1))
  let Q := d.tensor (a,d.tensor (d.tensor (b,c),e))
  let Q' := d.tensor (a,d.tensor (d.tensor (c,b),e))
  have hM : middleSwap d q=K*C*K⁻¹ := by
    change d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹=_
    have ht := tensor_conjugate d (1:H) d.a⁻¹ (1:H) (d.tensor (q.c,1))
    simp only [inv_one,mul_one,inv_inv] at ht
    rw [ht]
    dsimp [K,C]
    group
  have hCQ : C*Q*C⁻¹=Q' := by
    dsimp only [C,Q,Q']
    rw [← tensor_conjugate]
    simp only [one_mul,inv_one,mul_one]
    rw [← tensor_conjugate]
    simp only [one_mul,inv_one,mul_one,q.naturality]
  have hQ : K*Q*K⁻¹=d.tensor (d.tensor (a,b),d.tensor (c,e)) := reassociate_four d a b c e
  have hQ' : K*Q'*K⁻¹=d.tensor (d.tensor (a,c),d.tensor (b,e)) := reassociate_four d a c b e
  rw [hM,← hQ,← hQ']
  calc
    _=K*(C*Q*C⁻¹)*K⁻¹ := by group
    _=_ := by rw [hCQ]

lemma middleSwap_involutive : middleSwap d q*middleSwap d q=1 := by
  let K := d.a*d.tensor (1,d.a⁻¹)
  let C := d.tensor (1,d.tensor (q.c,1))
  have hM : middleSwap d q=K*C*K⁻¹ := by
    change d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹=_
    have ht := tensor_conjugate d (1:H) d.a⁻¹ (1:H) (d.tensor (q.c,1))
    simp only [inv_one,mul_one,inv_inv] at ht
    rw [ht]
    dsimp [K,C]
    group
  have hC : C*C=1 := by
    have h₁ : (1:H)*1=1 := one_mul 1
    have h₂ : d.tensor (q.c,1)*d.tensor (q.c,1)=1 := by
      rw [← map_mul]
      change d.tensor (q.c*q.c,(1:H)*1)=1
      rw [q.square,h₁]
      exact map_one d.tensor
    change d.tensor (1,d.tensor (q.c,1))*d.tensor (1,d.tensor (q.c,1))=1
    rw [← map_mul]
    change d.tensor ((1:H)*1,d.tensor (q.c,1)*d.tensor (q.c,1))=1
    rw [h₁,h₂]
    exact map_one d.tensor
  rw [hM]
  calc
    _=K*(C*C)*K⁻¹ := by group
    _=1 := by rw [hC,mul_one,mul_inv_cancel]

end

section
universe u
open CategoryTheory
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

/-- Adjacent swaps in a fixed left-associated triple. -/
def firstSwap : H := d.tensor (q.c,1)
def secondSwap : H := d.a*d.tensor (1,q.c)*d.a⁻¹

lemma adjacent_braid : firstSwap d q*secondSwap d q*firstSwap d q=
    secondSwap d q*firstSwap d q*secondSwap d q := by
  let := monoidal d
  let := symmetric d q
  have h := congrArg (fun f : (Object.positive : Object H) ⟶ Object.positive=>f.val)
    (CategoryTheory.BraidedCategory.yang_baxter (Object.positive : Object H) Object.positive Object.positive)
  simp only [comp_val] at h
  change ((((((d.a⁻¹ * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹) * d.tensor (1,q.c)) * d.a⁻¹) * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹)=
    (((d.tensor (1,q.c) * d.a⁻¹) * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹) * d.tensor (1,q.c) at h
  simp only [inv_inv] at h
  have hh := congrArg (fun z : H=>d.a*z*d.a⁻¹) h
  dsimp only [firstSwap,secondSwap]
  convert hh using 1 <;> group

lemma firstSwap_square : firstSwap d q*firstSwap d q=1 := by
  rw [firstSwap,← map_mul]
  change d.tensor (q.c*q.c,(1:H)*1)=1
  rw [q.square,one_mul]
  exact map_one d.tensor

lemma secondSwap_square : secondSwap d q*secondSwap d q=1 := by
  have h : d.tensor (1,q.c)*d.tensor (1,q.c)=1 := by
    rw [← map_mul]
    change d.tensor ((1:H)*1,q.c*q.c)=1
    rw [q.square,one_mul]
    exact map_one d.tensor
  dsimp only [secondSwap]
  calc
    _=d.a*(d.tensor (1,q.c)*d.tensor (1,q.c))*d.a⁻¹ := by group
    _=1 := by rw [h,mul_one,mul_inv_cancel]

end

/- General naturality of the adjacent permutations on decorated triples. -/
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma firstSwap_naturality (g h k : H) :
    firstSwap d q * d.tensor (d.tensor (g,h),k) * (firstSwap d q)⁻¹ =
      d.tensor (d.tensor (h,g),k) := by
  simp only [firstSwap,← map_inv,← map_mul,Prod.mk_mul_mk,Prod.inv_mk,
    inv_one,one_mul,mul_one,q.naturality]

lemma secondSwap_naturality (g h k : H) :
    secondSwap d q * d.tensor (d.tensor (g,h),k) * (secondSwap d q)⁻¹ =
      d.tensor (d.tensor (g,k),h) := by
  have hh : d.tensor (1,q.c)*d.tensor (g,d.tensor (h,k))*(d.tensor (1,q.c))⁻¹=
      d.tensor (g,d.tensor (k,h)) := by
    simp only [← map_inv,← map_mul,Prod.mk_mul_mk,Prod.inv_mk,
      inv_one,one_mul,mul_one,q.naturality]
  rw [← d.naturality g h k,← d.naturality g k h,secondSwap]
  calc
    _=d.a*(d.tensor (1,q.c)*d.tensor (g,d.tensor (h,k))*(d.tensor (1,q.c))⁻¹)*d.a⁻¹ := by group
    _=_ := congrArg (fun z : H=>d.a*z*d.a⁻¹) hh

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

end

end OAI
