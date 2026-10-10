import Mathlib
import OAI.GroupTheory.FiniteType.AscendingHNN

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace AscendingTorus

open Monoid.Coprod Multiplicative

universe u

variable {U : Type u} [Group U]

def relation (f : U →* U) (x : U) : Monoid.Coprod U (Multiplicative ℤ) :=
  inl x * inr (ofAdd 1) * (inl (f x))⁻¹ * (inr (ofAdd 1))⁻¹

abbrev relations (f : U →* U) : Subgroup (Monoid.Coprod U (Multiplicative ℤ)) :=
  Subgroup.normalClosure (Set.range (relation f))

abbrev Torus (f : U →* U) : Type u :=
  Monoid.Coprod U (Multiplicative ℤ) ⧸ relations f

def of (f : U →* U) : U →* Torus f :=
  (QuotientGroup.mk' (relations f)).comp inl

def t (f : U →* U) : Torus f :=
  QuotientGroup.mk' (relations f) (inr (ofAdd 1))

theorem of_mul_t (f : U →* U) (x : U) :
    of f x * t f = t f * of f (f x) := by
  have hr : QuotientGroup.mk' (relations f) (relation f x) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  have hr' : of f x * t f * (of f (f x))⁻¹ * (t f)⁻¹ = 1 := by
    change (QuotientGroup.mk' (relations f)) (inl x) *
      (QuotientGroup.mk' (relations f)) (inr (ofAdd 1)) *
      ((QuotientGroup.mk' (relations f)) (inl (f x)))⁻¹ *
      ((QuotientGroup.mk' (relations f)) (inr (ofAdd 1)))⁻¹ = 1
    simpa only [relation, map_mul, map_inv] using hr
  have h := congrArg (fun z => z * t f * of f (f x)) hr'
  simpa [mul_assoc] using h

variable {V : Type*} [Group V]

def lift (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) : Torus f →* V :=
  QuotientGroup.lift (relations f) (Monoid.Coprod.lift k (zpowersHom V s))
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨x, rfl⟩
      change Monoid.Coprod.lift k (zpowersHom V s) (relation f x) = 1
      simp only [relation, map_mul, map_inv, Monoid.Coprod.lift_apply_inl,
        Monoid.Coprod.lift_apply_inr]
      simp [hs x, mul_assoc]))

@[simp] theorem lift_of (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) (x : U) :
    lift f k s hs (of f x) = k x := by
  rfl

@[simp] theorem lift_t (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) :
    lift f k s hs (t f) = s := by
  change s ^ (1 : ℤ) = s
  exact zpow_one s

@[ext] theorem hom_ext (f : U →* U) {k l : Torus f →* V}
    (hU : k.comp (of f) = l.comp (of f)) (ht : k (t f) = l (t f)) : k = l := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f))).1
  exact Monoid.Coprod.hom_ext hU (MonoidHom.ext_mint ht)

theorem conj_of_image (f : U →* U) (x : U) :
    t f * of f (f x) * (t f)⁻¹ = of f x := by
  rw [← of_mul_t]
  simp [mul_assoc]

variable {P : Type*} [Group P]

def interleaveForward (a : U →* P) (b : P →* U) :
    Torus (b.comp a) →* Torus (a.comp b) :=
  lift (b.comp a) ((of (a.comp b)).comp a) (t (a.comp b)) (by
    intro x
    exact of_mul_t (a.comp b) (a x))

def interleaveBase (a : U →* P) (b : P →* U) : P →* Torus (b.comp a) :=
  (MulAut.conj (t (b.comp a))).toMonoidHom.comp ((of (b.comp a)).comp b)

@[simp] theorem interleaveBase_apply (a : U →* P) (b : P →* U) (x : P) :
    interleaveBase a b x =
      t (b.comp a) * of (b.comp a) (b x) * (t (b.comp a))⁻¹ := rfl

def interleaveBackward (a : U →* P) (b : P →* U) :
    Torus (a.comp b) →* Torus (b.comp a) :=
  lift (a.comp b) (interleaveBase a b) (t (b.comp a)) (by
    intro x
    change t (b.comp a) * of (b.comp a) (b x) * (t (b.comp a))⁻¹ * t (b.comp a) =
      t (b.comp a) * (t (b.comp a) * of (b.comp a) ((b.comp a) (b x)) *
        (t (b.comp a))⁻¹)
    rw [conj_of_image]
    simp [mul_assoc])

@[simp] theorem interleaveBackward_forward (a : U →* P) (b : P →* U) :
    (interleaveBackward a b).comp (interleaveForward a b) =
      MonoidHom.id (Torus (b.comp a)) := by
  apply hom_ext
  · ext x
    change interleaveBackward a b (interleaveForward a b (of (b.comp a) x)) =
      of (b.comp a) x
    simp only [interleaveForward, interleaveBackward, lift_of, MonoidHom.comp_apply,
      interleaveBase_apply]
    exact conj_of_image (b.comp a) x
  · simp [interleaveForward, interleaveBackward]

@[simp] theorem interleaveForward_backward (a : U →* P) (b : P →* U) :
    (interleaveForward a b).comp (interleaveBackward a b) =
      MonoidHom.id (Torus (a.comp b)) := by
  apply hom_ext
  · ext x
    change interleaveForward a b (interleaveBackward a b (of (a.comp b) x)) =
      of (a.comp b) x
    simp only [interleaveBackward, lift_of, interleaveBase_apply, map_mul, map_inv]
    simp only [interleaveForward, lift_t, lift_of, MonoidHom.comp_apply]
    exact conj_of_image (a.comp b) x
  · simp [interleaveForward, interleaveBackward]

def interleaveEquiv (a : U →* P) (b : P →* U) :
    Torus (b.comp a) ≃* Torus (a.comp b) where
  toFun := interleaveForward a b
  invFun := interleaveBackward a b
  left_inv x := DFunLike.congr_fun (interleaveBackward_forward a b) x
  right_inv x := DFunLike.congr_fun (interleaveForward_backward a b) x
  map_mul' := map_mul (interleaveForward a b)

theorem map_relation_eq_one_iff (f : U →* U)
    (q : Monoid.Coprod U (Multiplicative ℤ) →* V) (x : U) :
    q (relation f x) = 1 ↔
      q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹ := by
  simp only [relation, map_mul, map_inv]
  rw [mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul,
    ← eq_mul_inv_iff_mul_eq]

theorem normalClosure_relations_dense (f : U →* U) (S : Set U)
    (hS : Subgroup.closure S = ⊤) :
    relations f = Subgroup.normalClosure (relation f '' S) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    let N := Subgroup.normalClosure (relation f '' S)
    let q := QuotientGroup.mk' N
    have hconj : q.comp inl =
        (MulAut.conj (q (inr (ofAdd 1)))).toMonoidHom.comp ((q.comp inl).comp f) := by
      apply MonoidHom.eq_of_eqOn_dense hS
      intro x hx
      change q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹
      apply (map_relation_eq_one_iff f q x).1
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨x, hx, rfl⟩)
    rintro _ ⟨x, rfl⟩
    apply (QuotientGroup.eq_one_iff _).1
    apply (map_relation_eq_one_iff f q x).2
    exact DFunLike.congr_fun hconj x
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, _, rfl⟩
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩

theorem finitelyPresented (f : U →* U) [Group.IsFinitelyPresented U] :
    Group.IsFinitelyPresented (Torus f) := by
  obtain ⟨n, φ, hφ, _⟩ := (inferInstance : Group.IsFinitelyPresented U).out
  have : Group.FG U := Group.fg_of_surjective hφ
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG U)
  apply Group.IsFinitelyPresented.quotient
  exact ⟨relation f '' S, hfin.image _, (normalClosure_relations_dense f S hS).symm⟩

theorem finitelyPresented_of_factorization (f : U →* U)
    (a : U →* P) (b : P →* U) (hf : f = b.comp a)
    [Group.IsFinitelyPresented P] : Group.IsFinitelyPresented (Torus f) := by
  subst f
  have := finitelyPresented (a.comp b)
  exact Group.IsFinitelyPresented.equiv (interleaveEquiv a b).symm

end AscendingTorus

namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

def toPresentation : Torus f hf →* AscendingTorus.Torus f :=
  evaluation f hf (AscendingTorus.of f) (AscendingTorus.t f) (AscendingTorus.of_mul_t f)

def fromPresentation : AscendingTorus.Torus f →* Torus f hf :=
  AscendingTorus.lift f (embed f hf) (stable f hf) (embed_mul_stable f hf)

@[simp] lemma toPresentation_embed (u : U) :
    toPresentation f hf (embed f hf u)=AscendingTorus.of f u := evaluation_embed _ _ _ _ _ _
@[simp] lemma toPresentation_stable :
    toPresentation f hf (stable f hf)=AscendingTorus.t f := evaluation_stable _ _ _ _ _
@[simp] lemma fromPresentation_of (u : U) :
    fromPresentation f hf (AscendingTorus.of f u)=embed f hf u := AscendingTorus.lift_of _ _ _ _ _
@[simp] lemma fromPresentation_t :
    fromPresentation f hf (AscendingTorus.t f)=stable f hf := AscendingTorus.lift_t _ _ _ _

lemma from_to_presentation : (fromPresentation f hf).comp (toPresentation f hf)=MonoidHom.id _ := by
  apply hom_ext
  · intro u; simp
  · simp

lemma to_from_presentation : (toPresentation f hf).comp (fromPresentation f hf)=MonoidHom.id _ := by
  apply AscendingTorus.hom_ext
  · ext u; simp
  · simp

def presentationEquiv : Torus f hf ≃* AscendingTorus.Torus f where
  toFun := toPresentation f hf
  invFun := fromPresentation f hf
  left_inv g := DFunLike.congr_fun (from_to_presentation f hf) g
  right_inv g := DFunLike.congr_fun (to_from_presentation f hf) g
  map_mul' := (toPresentation f hf).map_mul

variable {P : Type*} [Group P] [Group.IsFinitelyPresented P]

theorem finitelyPresented_of_factorization (a : U →* P) (b : P →* U)
    (heq : f=b.comp a) : Group.IsFinitelyPresented (Torus f hf) := by
  let _ := AscendingTorus.finitelyPresented_of_factorization f a b heq
  exact Group.IsFinitelyPresented.equiv (presentationEquiv f hf).symm

end AscendingHNN

end

end OAI
