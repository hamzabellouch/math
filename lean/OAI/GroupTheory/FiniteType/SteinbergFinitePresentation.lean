import Mathlib
import OAI.GroupTheory.FiniteType.SteinbergWords
import OAI.GroupTheory.FiniteType.TorusAction

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace SteinbergFinitePresentation
open scoped commutatorElement
variable (n α : Type*)

abbrev Triple := {t : n×n×n // t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2}
abbrev Quad := {t : n×n×n×n // t.1≠t.2.1 ∧ t.2.2.1≠t.2.2.2 ∧
  t.1≠t.2.2.2 ∧ t.2.1≠t.2.2.1}
abbrev Index := (Quad n × Option α × Option α) ⊕ (Bool × Triple n × Option α)

private def letter (i j : n) (hij : i≠j) (a : Option α) : FreeGroup (Steinberg.Root n (Option α)) :=
  FreeGroup.of ⟨i,j,hij,a⟩

def relator : Index n α → FreeGroup (Steinberg.Root n (Option α))
  | .inl (q,a,b) =>
    ⁅letter n α q.1.1 q.1.2.1 q.2.1 a,
      letter n α q.1.2.2.1 q.1.2.2.2 q.2.2.1 b⁆
  | .inr (right,t,a) =>
    ⁅letter n α t.1.1 t.1.2.1 t.2.1 (if right then a else none),
      letter n α t.1.2.1 t.1.2.2 t.2.2.1 (if right then none else a)⁆*
      (letter n α t.1.1 t.1.2.2 t.2.2.2 a)⁻¹

def relations : Set (FreeGroup (Steinberg.Root n (Option α))) := Set.range (relator n α)
abbrev Universal := PresentedGroup (relations n α)

instance [Finite n] [Finite α] : Finite (Steinberg.Root n α) := by
  apply Finite.of_injective (fun r : Steinberg.Root n α => (r.i,r.j,r.coefficient))
  rintro ⟨i,j,hij,a⟩ ⟨k,l,hkl,b⟩ he
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl,rfl,rfl⟩
  rfl

instance [Finite n] [Finite α] : Finite (relations n α) :=
  (Set.finite_range (relator n α)).to_subtype
instance [Finite n] [Finite α] : Group.IsFinitelyPresented (Universal n α) := inferInstance

private lemma relator_eq_one (r : Index n α) :
    PresentedGroup.mk (relations n α) (relator n α r)=1 :=
  PresentedGroup.one_of_mem ⟨r,rfl⟩

def initial : SteinbergWords.Initial (n:=n) (α:=α) (H:=Universal n α) where
  gen i j hij a := PresentedGroup.of ⟨i,j,hij,a⟩
  away i j k l hij hkl hil hjk a b := by
    apply commutatorElement_eq_one_iff_commute.mp
    exact relator_eq_one n α (.inl (⟨(i,j,k,l),⟨hij,hkl,hil,hjk⟩⟩,a,b))
  chain_left i j k hij hjk hik a := by
    have he := relator_eq_one n α (.inr (false,⟨(i,j,k),⟨hij,hjk,hik⟩⟩,a))
    simpa only [relator,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,map_commutatorElement,
      letter,PresentedGroup.of,mul_inv_eq_one] using he
  chain_right i j k hij hjk hik a := by
    have he := relator_eq_one n α (.inr (true,⟨(i,j,k),⟨hij,hjk,hik⟩⟩,a))
    simpa only [relator,↓reduceIte,map_mul,map_inv,map_commutatorElement,
      letter,PresentedGroup.of,mul_inv_eq_one] using he

abbrev Coeff := FreeAbelianGroup (FreeMonoid α)
def coefficient : Option α → Coeff α
  | none => 1
  | some a => FreeAbelianGroup.of (FreeMonoid.of a)

def toSteinberg : Universal n α →* Steinberg.Group n (Coeff α) :=
  PresentedGroup.toGroup (f:=fun r : Steinberg.Root n (Option α) =>
    Steinberg.root r.i r.j r.different (coefficient α r.coefficient)) (by
    rintro _ ⟨r,rfl⟩
    cases r with
    | inl q =>
      rcases q with ⟨q,a,b⟩
      simp only [relator,letter,map_commutatorElement,FreeGroup.lift_apply_of]
      exact (Steinberg.root_commute _ _ _ _ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 _ _).commutator_eq
    | inr t =>
      rcases t with ⟨right,t,a⟩
      cases right <;>
        simp only [relator,Bool.false_eq_true,↓reduceIte,letter,map_mul,map_inv,
          map_commutatorElement,FreeGroup.lift_apply_of]
      · rw [Steinberg.root_commutator _ _ _ t.2.1 t.2.2.1 t.2.2.2]
        simp only [coefficient,one_mul,mul_inv_cancel]
      · rw [Steinberg.root_commutator _ _ _ t.2.1 t.2.2.1 t.2.2.2]
        simp only [coefficient,mul_one,mul_inv_cancel])

@[simp] lemma toSteinberg_gen (i j : n) (hij : i≠j) (a : Option α) :
    toSteinberg n α ((initial n α).gen i j hij a)=
      Steinberg.root i j hij (coefficient α a) := PresentedGroup.toGroup.of _

variable (outside : ∀ i j k l : n, ∃ p, p≠i ∧ p≠j ∧ p≠k ∧ p≠l)

def fromSteinberg : Steinberg.Group n (Coeff α) →* Universal n α :=
  Steinberg.lift (SteinbergWords.polynomial outside (initial n α))
    (fun i j h a b => (SteinbergWords.polynomial_add outside (initial n α) i j h a b).symm)
    (SteinbergWords.polynomial_chain outside (initial n α))
    (SteinbergWords.polynomial_commute outside (initial n α))

lemma polynomial_coefficient (i j : n) (hij : i≠j) (a : Option α) :
    SteinbergWords.polynomial outside (initial n α) i j hij (coefficient α a)=
      (initial n α).gen i j hij a := by
  cases a with
  | none =>
    change SteinbergWords.polynomial outside (initial n α) i j hij (FreeAbelianGroup.of 1)=_
    rw [SteinbergWords.polynomial_of]
    exact SteinbergWords.word_nil outside (initial n α) i j hij
  | some a =>
    rw [coefficient,SteinbergWords.polynomial_of]
    exact SteinbergWords.word_singleton outside (initial n α) i j hij a

lemma from_to : (fromSteinberg n α outside).comp (toSteinberg n α)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨i,j,hij,a⟩
  change fromSteinberg n α outside (toSteinberg n α ((initial n α).gen i j hij a))=_
  rw [toSteinberg_gen,fromSteinberg,Steinberg.lift_root]
  exact polynomial_coefficient n α outside i j hij a

lemma toSteinberg_word (w : List α) (i j : n) (hij : i≠j) :
    toSteinberg n α (SteinbergWords.word outside (initial n α) i j hij w)=
      Steinberg.root (R:=Coeff α) i j hij (FreeAbelianGroup.of (FreeMonoid.ofList w)) := by
  induction w generalizing i j with
  | nil => exact toSteinberg_gen n α i j hij none
  | cons a w ih =>
    obtain ⟨k,hki,hkj,-,-⟩ := outside i j i j
    have he := SteinbergWords.word_chain outside (initial n α) [a] w i k j hki.symm hkj hij
    rw [List.singleton_append] at he
    rw [← he,map_commutatorElement,SteinbergWords.word_singleton,toSteinberg_gen,ih,
      Steinberg.root_commutator _ _ _ hki.symm hkj hij]
    change Steinberg.root i j hij (FreeAbelianGroup.of (FreeMonoid.of a)*
        FreeAbelianGroup.of (FreeMonoid.ofList w))=_
    rw [FreeAbelianGroup.of_mul_of]
    rfl

lemma toSteinberg_polynomial (i j : n) (hij : i≠j) (a : Coeff α) :
    toSteinberg n α (SteinbergWords.polynomial outside (initial n α) i j hij a)=
      Steinberg.root i j hij a := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of w =>
    rw [SteinbergWords.polynomial_of]
    exact toSteinberg_word n α outside w i j hij
  | neg a ha =>
    rw [SteinbergWords.polynomial_neg,map_inv,ha,Steinberg.root_neg]
  | add a b ha hb =>
    rw [SteinbergWords.polynomial_add,map_mul,ha,hb,Steinberg.root_add]

lemma to_from : (toSteinberg n α).comp (fromSteinberg n α outside)=MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro i j hij a
  change toSteinberg n α (fromSteinberg n α outside (Steinberg.root i j hij a))=_
  rw [fromSteinberg,Steinberg.lift_root]
  exact toSteinberg_polynomial n α outside i j hij a

def equiv : Universal n α ≃* Steinberg.Group n (Coeff α) where
  toFun := toSteinberg n α
  invFun := fromSteinberg n α outside
  left_inv x := DFunLike.congr_fun (from_to n α outside) x
  right_inv x := DFunLike.congr_fun (to_from n α outside) x
  map_mul' := (toSteinberg n α).map_mul

include outside in

theorem free_finitelyPresented [Finite n] [Finite α] :
    Group.IsFinitelyPresented (Steinberg.Group n (Coeff α)) :=
  Group.IsFinitelyPresented.equiv (equiv n α outside)

include outside in

theorem finitelyPresented [Finite n] [Finite α] {R : Type*} [Ring R]
    (φ : Coeff α →ₙ+* R) (hφ : Function.Surjective φ)
    (s : Set (Coeff α)) (hs : s.Finite)
    (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set (Coeff α))) :
    Group.IsFinitelyPresented (Steinberg.Group n R) := by
  let := free_finitelyPresented n α outside
  apply Steinberg.finitelyPresented_quotient (fun i j _ => ?_) φ hφ s hs hker
  obtain ⟨p,hpi,hpj,-,-⟩ := outside i j i j
  exact ⟨p,hpi.symm,hpj⟩

lemma fin_six_outside (i j k l : Fin 6) :
    ∃ p : Fin 6, p≠i ∧ p≠j ∧ p≠k ∧ p≠l := by
  classical
  have hn : ({i,j,k,l} : Finset (Fin 6))≠Finset.univ := by
    apply (Finset.card_lt_iff_ne_univ _).mp
    have h := (Finset.card_le_four (a:=i) (b:=j) (c:=k) (d:=l))
    simp only [Fintype.card_fin]
    omega
  have hp : ∃ p : Fin 6, p∉({i,j,k,l} : Finset (Fin 6)) := by
    by_contra h
    apply hn
    apply Finset.eq_univ_iff_forall.mpr
    simpa only [not_exists,not_not] using h
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hp

theorem rank_six_finitelyPresented [Finite α] {R : Type*} [Ring R]
    (φ : Coeff α →ₙ+* R) (hφ : Function.Surjective φ)
    (s : Set (Coeff α)) (hs : s.Finite)
    (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set (Coeff α))) :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R) :=
  finitelyPresented (Fin 6) α fin_six_outside φ hφ s hs hker

end SteinbergFinitePresentation
end

namespace HNNSubgroup
open AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)
variable (K : Subgroup (Torus f hf)) (ht : AscendingHNN.stable f hf ∈ K)

abbrev base : Subgroup U := K.comap (embed f hf)

include ht in
lemma base_invariant {u : U} (hu : u ∈ base f hf K) : f u ∈ base f hf K := by
  change embed f hf (f u) ∈ K
  have he : embed f hf (f u) = (stable f hf)⁻¹ * embed f hf u * stable f hf := by
    rw [mul_assoc,embed_mul_stable]
    group
  rw [he]
  exact K.mul_mem (K.mul_mem (K.inv_mem ht) hu) ht

def baseMap : base f hf K →* base f hf K where
  toFun u := ⟨f u,base_invariant f hf K ht u.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' u v := Subtype.ext (f.map_mul u v)

lemma baseMap_injective : Function.Injective (baseMap f hf K ht) := by
  intro u v huv
  exact Subtype.ext (hf (congrArg Subtype.val huv))

def inclusion : base f hf K →* K where
  toFun u := ⟨embed f hf u,u.property⟩
  map_one' := Subtype.ext ((embed f hf).map_one)
  map_mul' u v := Subtype.ext ((embed f hf).map_mul u.val v.val)

def stableElement : K := ⟨AscendingHNN.stable f hf,ht⟩

lemma inclusion_relation (u : base f hf K) :
    inclusion f hf K u * stableElement f hf K ht =
      stableElement f hf K ht * inclusion f hf K (baseMap f hf K ht u) :=
  Subtype.ext (embed_mul_stable f hf u)

def hom : Torus (baseMap f hf K ht) (baseMap_injective f hf K ht) →* K :=
  evaluation (baseMap f hf K ht) (baseMap_injective f hf K ht)
    (inclusion f hf K) (stableElement f hf K ht) (inclusion_relation f hf K ht)

lemma hom_injective : Function.Injective (hom f hf K ht) := by
  apply evaluation_injective (β := (heightHom f hf).comp K.subtype)
  · intro u v huv
    exact Subtype.ext (embed_injective f hf (congrArg Subtype.val huv))
  · intro u
    apply Multiplicative.toAdd.injective
    exact height_embed f hf u
  · apply Multiplicative.toAdd.injective
    exact height_stable f hf

lemma hom_surjective : Function.Surjective (hom f hf K ht) := by
  apply evaluation_surjective
  intro g
  obtain ⟨a,b,u,hu⟩ := normal_form f hf g.val
  have hm : u ∈ base f hf K := by
    change embed f hf u ∈ K
    have he : embed f hf u = ((AscendingHNN.stable f hf)^a)⁻¹ * g.val *
        (AscendingHNN.stable f hf)^b := by rw [hu]; group
    rw [he]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem ht a)) g.property) (K.pow_mem ht b)
  exact ⟨a,b,⟨u,hm⟩,Subtype.ext hu⟩

def equiv : Torus (baseMap f hf K ht) (baseMap_injective f hf K ht) ≃* K :=
  MulEquiv.ofBijective (hom f hf K ht) ⟨hom_injective f hf K ht,hom_surjective f hf K ht⟩

end HNNSubgroup

end

end OAI
