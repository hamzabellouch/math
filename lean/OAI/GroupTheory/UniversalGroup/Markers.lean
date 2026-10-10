import OAI.GroupTheory.UniversalGroup.FiniteHNN

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.DecoratedMarker
open Monoid Coprod
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

abbrev Kernel (G : Type u) [Group G] (T : Type v) (Q : Type w) :=
  G ∗ FreeGroup (T × Q)
abbrev Base (G : Type u) [Group G] (T : Type v) [Group T] (Q : Type w) :=
  (G × T) ∗ FreeGroup Q

def shift (t : T) : MulAut (Kernel G T Q) :=
  (MulEquiv.refl G).coprodCongr
    (FreeGroup.freeGroupCongr ((Equiv.mulLeft t).prodCongr (Equiv.refl Q)))

@[simp] theorem shift_inl (t : T) (g : G) : shift t (inl g : Kernel G T Q) = inl g := rfl
@[simp] theorem shift_inr_of (t s : T) (q : Q) :
    shift t (inr (FreeGroup.of (s,q)) : Kernel G T Q) = inr (FreeGroup.of (t*s,q)) := rfl

def shifts : T →* MulAut (Kernel G T Q) where
  toFun := shift
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp
    · apply FreeGroup.ext_hom
      rintro ⟨s,q⟩
      simp
  map_mul' t s := by
    apply MulEquiv.toMonoidHom_injective
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp
    · apply FreeGroup.ext_hom
      rintro ⟨r,q⟩
      simp [mul_assoc]

abbrev ShiftGroup (G : Type u) [Group G] (T : Type v) [Group T] (Q : Type w) :=
  (Kernel G T Q) ⋊[shifts] T

def coefficient : G →* Base G T Q := inl.comp (MonoidHom.inl G T)
def translation : T →* Base G T Q := inl.comp (MonoidHom.inr G T)
def marker (t : T) (q : Q) : Base G T Q :=
  translation t * inr (FreeGroup.of q) * (translation t)⁻¹

def inclusion : Kernel G T Q →* Base G T Q :=
  Coprod.lift coefficient (FreeGroup.lift (fun p ↦ marker p.1 p.2))

@[simp] theorem inclusion_inl (g : G) : inclusion (inl g : Kernel G T Q) = coefficient g := by
  simp [inclusion]
@[simp] theorem inclusion_inr_of (t : T) (q : Q) :
    inclusion (inr (FreeGroup.of (t,q)) : Kernel G T Q) = marker t q := by
  simp [inclusion]

lemma commute_coefficient_translation (g : G) (t : T) :
    Commute (coefficient g : Base G T Q) (translation t) :=
  (MonoidHom.commute_inl_inr g t).map inl

lemma test_commute (g : G) (t : T) :
    Commute (SemidirectProduct.inl (inl g) : ShiftGroup G T Q)
      (SemidirectProduct.inr t) := by
  apply SemidirectProduct.ext
  · change inl g * shifts (1 : T) 1 = 1 * shifts t (inl g)
    simp only [map_one, mul_one, one_mul]
    rfl
  · change (1 : T) * t = t * 1
    simp

def test : Base G T Q →* ShiftGroup G T Q :=
  Coprod.lift
    ((SemidirectProduct.inl.comp inl).noncommCoprod SemidirectProduct.inr test_commute)
    (FreeGroup.lift (fun q ↦ SemidirectProduct.inl (inr (FreeGroup.of (1,q)))))

@[simp] theorem test_coefficient (g : G) : test (coefficient g : Base G T Q) =
    SemidirectProduct.inl (inl g) := by simp [test,coefficient]
@[simp] theorem test_translation (t : T) : test (translation t : Base G T Q) =
    SemidirectProduct.inr t := by simp [test,translation]
@[simp] theorem test_inr_of (q : Q) : test (inr (FreeGroup.of q) : Base G T Q) =
    SemidirectProduct.inl (inr (FreeGroup.of (1,q))) := by simp [test]
@[simp] theorem test_marker (t : T) (q : Q) : test (marker t q : Base G T Q) =
    SemidirectProduct.inl (inr (FreeGroup.of (t,q))) := by
  simp only [marker,map_mul,map_inv,test_translation,test_inr_of]
  rw [← map_inv,← SemidirectProduct.inl_aut]
  change SemidirectProduct.inl (inr (FreeGroup.of (t * 1, q))) = _
  rw [mul_one]

@[simp] theorem test_comp : (test (G := G) (T := T) (Q := Q)).comp inclusion =
    SemidirectProduct.inl := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp
  · apply FreeGroup.ext_hom
    rintro ⟨t,q⟩
    simp

theorem inclusion_injective : Function.Injective (inclusion (G := G) (T := T) (Q := Q)) := by
  apply Function.Injective.of_comp (f := test)
  rw [← MonoidHom.coe_comp,test_comp]
  exact SemidirectProduct.inl_injective

lemma inclusion_shift (t : T) :
    (inclusion (G := G) (Q := Q)).comp (shifts t).toMonoidHom =
      (MulAut.conj (translation t)).toMonoidHom.comp inclusion := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,shifts,MonoidHom.coe_mk,
      OneHom.coe_mk,shift_inl,inclusion_inl,MulAut.conj_apply]
    rw [← (commute_coefficient_translation g t).eq,mul_inv_cancel_right]
  · apply FreeGroup.ext_hom
    rintro ⟨s,q⟩
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,shifts,MonoidHom.coe_mk,
      OneHom.coe_mk,shift_inr_of,inclusion_inr_of,MulAut.conj_apply,marker,map_mul,map_inv]
    group

def inverse : ShiftGroup G T Q →* Base G T Q :=
  SemidirectProduct.lift inclusion translation inclusion_shift

@[simp] theorem inverse_inl (x : Kernel G T Q) :
    inverse (SemidirectProduct.inl x) = inclusion x := by simp [inverse]
@[simp] theorem inverse_inr (t : T) :
    inverse (SemidirectProduct.inr t : ShiftGroup G T Q) = translation t := by simp [inverse]

@[simp] theorem inverse_comp_test : (inverse (G := G) (T := T) (Q := Q)).comp test =
    MonoidHom.id _ := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    rintro ⟨g,t⟩
    have he : (inl (g,t) : Base G T Q) = coefficient g * translation t := by
      rw [coefficient,translation,MonoidHom.comp_apply,MonoidHom.comp_apply,← map_mul]
      simp
    change inverse (test (inl (g,t))) = inl (g,t)
    rw [he]
    simp
  · apply FreeGroup.ext_hom
    intro q
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply,test_inr_of,inverse_inl,
      inclusion_inr_of,marker,map_one,one_mul,inv_one,mul_one]

@[simp] theorem test_comp_inverse : (test (G := G) (T := T) (Q := Q)).comp inverse =
    MonoidHom.id _ := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,inverse_inl,MonoidHom.id_apply]
    exact DFunLike.congr_fun test_comp x
  · apply MonoidHom.ext
    intro t
    simp

def decomposition : Base G T Q ≃* ShiftGroup G T Q :=
  MonoidHom.toMulEquiv test inverse inverse_comp_test test_comp_inverse

end Higman.DecoratedMarker

namespace Higman.DecoratedFreeBasis
open Monoid Coprod
variable {G : Type*} [Group G] {X : Type*}

def inclusion (w : X → G) : FreeGroup X →* G ∗ FreeGroup X :=
  FreeGroup.lift (fun x ↦ inl (w x) * inr (FreeGroup.of x))

@[simp] theorem inclusion_of (w : X → G) (x : X) :
    inclusion w (FreeGroup.of x) = inl (w x) * inr (FreeGroup.of x) := by
  simp [inclusion]

@[simp] theorem projection_comp (w : X → G) :
    (Coprod.snd : G ∗ FreeGroup X →* FreeGroup X).comp (inclusion w) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro x
  simp

theorem inclusion_injective (w : X → G) : Function.Injective (inclusion w) := by
  apply Function.Injective.of_comp (f := (Coprod.snd : G ∗ FreeGroup X →* FreeGroup X))
  rw [← MonoidHom.coe_comp,projection_comp]
  exact Function.injective_id

def twist (w : X → G) : MulAut (G ∗ FreeGroup X) :=
  MonoidHom.toMulEquiv
    (Coprod.lift inl (inclusion w))
    (Coprod.lift inl (inclusion (fun x ↦ (w x)⁻¹)))
    (by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp
      · apply FreeGroup.ext_hom
        intro x
        simp)
    (by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp
      · apply FreeGroup.ext_hom
        intro x
        simp)

@[simp] theorem twist_inl (w : X → G) (g : G) : twist w (inl g) = inl g := by
  simp [twist]
@[simp] theorem twist_inr_of (w : X → G) (x : X) : twist w (inr (FreeGroup.of x)) =
    inl (w x) * inr (FreeGroup.of x) := by simp [twist]

end Higman.DecoratedFreeBasis

namespace Higman.MarkerEmbedding
open Monoid Coprod DecoratedMarker
variable {G : Type u} [Group G] {D : Type v} [Group D]
    {T : Type w} [Group T] {P Q : Type*}

def index (f : D →* T) (o : P → T) (q : P → Q) (x : D × P) : T × Q :=
  (f x.1 * o x.2,q x.2)

def kernelMap (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    Kernel G D P →* Kernel G T Q :=
  Coprod.lift inl (FreeGroup.lift (fun x : D × P ↦
    inl (w x.2) * inr (FreeGroup.of (index f o q x))))

@[simp] theorem kernelMap_inl (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (g : G) :
    kernelMap f o q w (inl g) = inl g := by simp [kernelMap]
@[simp] theorem kernelMap_inr_of (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (x : D × P) :
    kernelMap f o q w (inr (FreeGroup.of x)) =
      inl (w x.2) * inr (FreeGroup.of (index f o q x)) := by simp [kernelMap]

lemma kernelMap_shift (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (d : D) :
    (kernelMap f o q w).comp (shifts d).toMonoidHom =
      (shifts (f d)).toMonoidHom.comp (kernelMap f o q w) := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp [shifts]
  · apply FreeGroup.ext_hom
    rintro ⟨e,p⟩
    simp [shifts,index,mul_assoc]

def embedding (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    Base G D P →* Base G T Q :=
  inverse.comp ((SemidirectProduct.map (kernelMap f o q w) f
    (kernelMap_shift f o q w)).comp test)

@[simp] theorem embedding_coefficient (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (g : G) : embedding f o q w (coefficient g) = coefficient g := by
  simp [embedding]
@[simp] theorem embedding_translation (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (d : D) : embedding f o q w (translation d) = translation (f d) := by
  simp [embedding]
@[simp] theorem embedding_inr_of (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (p : P) : embedding f o q w (inr (FreeGroup.of p)) = coefficient (w p) * marker (o p) (q p) := by
  simp [embedding,index]
@[simp] theorem embedding_marker (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (d : D) (p : P) : embedding f o q w (marker d p) =
      coefficient (w p) * marker (f d * o p) (q p) := by
  simp only [embedding,MonoidHom.comp_apply,test_marker,SemidirectProduct.map_inl,
    kernelMap_inr_of,inverse_inl,map_mul,inclusion_inl,inclusion_inr_of,index]

theorem kernelMap_injective [Nonempty P] (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (hi : Function.Injective (index f o q)) :
    Function.Injective (kernelMap f o q w) := by
  classical
  let r := Function.invFun (index f o q)
  have hr : Function.LeftInverse r (index f o q) := Function.leftInverse_invFun hi
  let k := Coprod.map (MonoidHom.id G) (FreeGroup.map (index f o q))
  have hk : Function.Injective k := by
    let l := Coprod.map (MonoidHom.id G) (FreeGroup.map r)
    have he : l.comp k = MonoidHom.id _ := by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp [l,k]
      · apply FreeGroup.ext_hom
        intro x
        simp [l,k,hr x]
    apply Function.Injective.of_comp (f := l)
    rw [← MonoidHom.coe_comp,he]
    exact Function.injective_id
  have he : kernelMap f o q w = k.comp (DecoratedFreeBasis.twist (w ∘ Prod.snd)).toMonoidHom := by
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp [k]
    · apply FreeGroup.ext_hom
      intro x
      simp [k]
  rw [he]
  exact hk.comp (DecoratedFreeBasis.twist (w ∘ Prod.snd)).injective

theorem embedding_injective [Nonempty P] (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (hi : Function.Injective (index f o q)) :
    Function.Injective (embedding f o q w) := by
  have hk := kernelMap_injective f o q w hi
  have hm : Function.Injective (SemidirectProduct.map (kernelMap f o q w) f
      (kernelMap_shift f o q w)) := by
    intro x y he
    apply SemidirectProduct.ext
    · exact hk (congrArg SemidirectProduct.left he)
    · exact hf (congrArg SemidirectProduct.right he)
  exact (decomposition (G := G) (T := T) (Q := Q)).symm.injective.comp
    (hm.comp (decomposition (G := G) (T := D) (Q := P)).injective)

theorem index_injective (f : D →* T) (hf : Function.Injective f) (o : P → T)
    (q : P → Q) (hq : Function.Injective q) : Function.Injective (index f o q) := by
  rintro ⟨d,p⟩ ⟨e,r⟩ he
  obtain rfl : p = r := hq (congrArg Prod.snd he)
  have hd : f d * o p = f e * o p := congrArg Prod.fst he
  exact Prod.ext (hf (mul_right_cancel hd)) rfl

end Higman.MarkerEmbedding

end UniversalFinitelyPresentedProof

end OAI
