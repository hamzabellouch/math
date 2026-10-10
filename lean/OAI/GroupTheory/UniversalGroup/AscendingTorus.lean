import OAI.GroupTheory.UniversalGroup.GraphActions

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.AscendingTorus

section

open Monoid Coprod Multiplicative
universe u v w
variable {U : Type u} [Group U]

abbrev Free (U : Type u) [Group U] := U ∗ Multiplicative ℤ

def letter : Free U := inr (ofAdd 1)

def relation (f : Monoid.End U) (x : U) : Free U :=
  (inl x * letter) * (letter * inl (f x))⁻¹

def relations (f : Monoid.End U) : Subgroup (Free U) :=
  Subgroup.normalClosure (Set.range (relation f))

instance (f : Monoid.End U) : (relations f).Normal := inferInstanceAs
  (Subgroup.normalClosure (Set.range (relation f))).Normal

def Torus (f : Monoid.End U) := Free U ⧸ relations f

instance (f : Monoid.End U) : Group (Torus f) := by
  delta Torus
  infer_instance

instance groupOfHom (f : U →* U) : Group (Torus f) := instGroupTorus f

def of (f : Monoid.End U) : U →* Torus f :=
  (QuotientGroup.mk' (relations f)).comp inl

def stable (f : Monoid.End U) : Torus f :=
  QuotientGroup.mk' (relations f) letter

lemma of_mul_stable (f : Monoid.End U) (x : U) :
    of f x * stable f = stable f * of f (f x) := by
  apply mul_inv_eq_one.mp
  change QuotientGroup.mk' (relations f) (relation f x) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x,rfl⟩)

lemma stable_conjugate (f : Monoid.End U) (x : U) :
    stable f * of f (f x) * (stable f)⁻¹ = of f x := by
  rw [← of_mul_stable, mul_inv_cancel_right]

lemma inverse_conjugate (f : Monoid.End U) (x : U) :
    (stable f)⁻¹ * of f x * stable f = of f (f x) := by
  rw [mul_assoc, of_mul_stable, inv_mul_cancel_left]

variable {V : Type v} [Group V]

def lift (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) : Torus f →* V :=
  QuotientGroup.lift (relations f) (Coprod.lift φ (zpowersHom V t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x,rfl⟩
    change Coprod.lift φ (zpowersHom V t) (relation f x) = 1
    simp only [relation, letter, map_mul, map_inv, Coprod.lift_apply_inl, Coprod.lift_apply_inr,
      zpowersHom_apply, toAdd_ofAdd, zpow_one]
    rw [h x, mul_inv_cancel])

@[simp] lemma lift_of (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) (x : U) :
    lift f φ t h (of f x) = φ x := by
  change Coprod.lift φ (zpowersHom V t) (inl x) = _
  simp

@[simp] lemma lift_stable (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) :
    lift f φ t h (stable f) = t := by
  change Coprod.lift φ (zpowersHom V t) (inr (ofAdd 1)) = _
  simp

@[ext] lemma hom_ext {f : Monoid.End U} {φ ψ : Torus f →* V}
    (ho : φ.comp (of f) = ψ.comp (of f)) (ht : φ (stable f) = ψ (stable f)) :
    φ = ψ := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f))).mp
  apply Coprod.hom_ext ho
  exact MonoidHom.ext_mint ht

theorem of_injective (f : Monoid.End U) (hf : Function.Injective f) :
    Function.Injective (of f) := by
  let e : (⊤ : Subgroup U) ≃* f.range :=
    (Subgroup.topEquiv).trans (MonoidHom.ofInjective hf)
  let H := HNNExtension U ⊤ f.range e
  let j : U →* H := HNNExtension.of
  let s : H := HNNExtension.t
  have hs (x : U) : j x * s⁻¹ = s⁻¹ * j (f x) := by
    exact HNNExtension.of_mul_inv_t (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup U))
  let Φ : Torus f →* H := lift f j s⁻¹ hs
  intro x y hxy
  apply HNNExtension.of_injective (A := ⊤) (B := f.range) (φ := e)
  exact (lift_of f j s⁻¹ hs x).symm.trans
    ((congrArg Φ hxy).trans (lift_of f j s⁻¹ hs y))

section Factorization
variable {P : Type v} [Group P] (a : U →* P) (b : P →* U)

def forward : Torus (b.comp a) →* Torus (a.comp b) :=
  lift (b.comp a) ((of (a.comp b)).comp a) (stable (a.comp b))
    (fun x => of_mul_stable (a.comp b) (a x))

def backward : Torus (a.comp b) →* Torus (b.comp a) :=
  lift (a.comp b)
    ((MulAut.conj (stable (b.comp a))).toMonoidHom.comp ((of (b.comp a)).comp b))
    (stable (b.comp a)) (by
      intro p
      change (stable (b.comp a) * of (b.comp a) (b p) * (stable (b.comp a))⁻¹) *
        stable (b.comp a) = stable (b.comp a) *
          (stable (b.comp a) * of (b.comp a) ((b.comp a) (b p)) * (stable (b.comp a))⁻¹)
      exact (inv_mul_cancel_right _ _).trans
        (congrArg (stable (b.comp a) * ·) (stable_conjugate (b.comp a) (b p)).symm))

@[simp] lemma forward_of (x : U) :
    forward a b (of (b.comp a) x) = of (a.comp b) (a x) :=
  lift_of _ _ _ _ x

@[simp] lemma forward_stable :
    forward a b (stable (b.comp a)) = stable (a.comp b) := lift_stable _ _ _ _

@[simp] lemma backward_of (p : P) :
    backward a b (of (a.comp b) p) =
      stable (b.comp a) * of (b.comp a) (b p) * (stable (b.comp a))⁻¹ :=
  lift_of _ _ _ _ p

@[simp] lemma backward_stable :
    backward a b (stable (a.comp b)) = stable (b.comp a) := lift_stable _ _ _ _

lemma backward_forward : (backward a b).comp (forward a b) = MonoidHom.id _ := by
  apply hom_ext
  · ext x
    simp only [MonoidHom.comp_apply, forward_of, backward_of, MonoidHom.id_apply]
    exact stable_conjugate (b.comp a) x
  · simp

lemma forward_backward : (forward a b).comp (backward a b) = MonoidHom.id _ := by
  apply hom_ext
  · ext p
    simp only [MonoidHom.comp_apply, backward_of, map_mul, map_inv, forward_stable,
      forward_of, MonoidHom.id_apply]
    exact stable_conjugate (a.comp b) p
  · simp

def cyclicFactorization : Torus (b.comp a) ≃* Torus (a.comp b) :=
  { forward a b with
    invFun := backward a b
    left_inv := fun x => DFunLike.congr_fun (backward_forward a b) x
    right_inv := fun x => DFunLike.congr_fun (forward_backward a b) x }

end Factorization

lemma relations_finitelyNormallyGenerated [Group.FG U] (f : Monoid.End U) :
    (relations f).IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup U).FG)
  let N : Subgroup (Free U) := Subgroup.normalClosure (relation f '' (S : Set U))
  let Q := Free U ⧸ N
  let q : Free U →* Q := QuotientGroup.mk' N
  let t : Q := q letter
  let i : U →* Q := q.comp inl
  let j : U →* Q := (MulAut.conj t).toMonoidHom.comp (i.comp f)
  let E : Subgroup U :=
    { carrier := {x | i x = j x}
      one_mem' := by simp only [Set.mem_ofPred_eq,map_one]
      mul_mem' := by
        intro x y hx hy
        change i (x*y) = j (x*y)
        rw [map_mul,map_mul,hx,hy]
      inv_mem' := by
        intro x hx
        change i x⁻¹ = j x⁻¹
        rw [map_inv,map_inv,hx] }
  have hSsub : (S : Set U) ⊆ E := by
    intro x hx
    have hw : q (relation f x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x,hx,rfl⟩)
    have he : i x * t = t * i (f x) := by
      apply mul_inv_eq_one.mp
      exact hw
    change i x = t * i (f x) * t⁻¹
    rw [← he,mul_inv_cancel_right]
  have htop : (⊤ : Subgroup U) ≤ E := by
    rw [← hS]
    exact (Subgroup.closure_le _).mpr hSsub
  have he (x : U) : i x = t * i (f x) * t⁻¹ := htop (Subgroup.mem_top x)
  refine ⟨relation f '' (S : Set U), S.finite_toSet.image _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨x,_,rfl⟩
    exact ⟨x,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change (i x * t) * (t * i (f x))⁻¹ = 1
    rw [mul_inv_eq_one]
    rw [he x,inv_mul_cancel_right]

instance finitelyPresented [Group.IsFinitelyPresented U] (f : Monoid.End U) :
    Group.IsFinitelyPresented (Torus f) := by
  obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented U).out
  let : Group.FG U := Group.fg_of_surjective hφ
  exact Group.IsFinitelyPresented.quotient (relations f) (relations_finitelyNormallyGenerated f)

theorem finitelyPresented_of_factorization {P : Type v} [Group P]
    [Group.IsFinitelyPresented P] (a : U →* P) (b : P →* U) :
    Group.IsFinitelyPresented (Torus (b.comp a)) := by
  let : Group.IsFinitelyPresented (Torus (a.comp b)) := finitelyPresented (a.comp b)
  exact Group.IsFinitelyPresented.equiv (cyclicFactorization a b).symm

end

section
open Monoid Coprod Multiplicative
universe u
variable {U : Type u} [Group U]

lemma of_mul_stable_pow (f : Monoid.End U) (u : U) (n : ℕ) :
    of f u * stable f ^ n = stable f ^ n * of f ((f ^ n) u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, of_mul_stable, ← mul_assoc, ← pow_succ]
    rw [pow_succ' f n]
    rfl

lemma inv_stable_pow_mul_of (f : Monoid.End U) (u : U) (n : ℕ) :
    (stable f ^ n)⁻¹ * of f u = of f ((f ^ n) u) * (stable f ^ n)⁻¹ := by
  apply mul_right_cancel (b := stable f ^ n)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [of_mul_stable_pow, inv_mul_cancel_left]

def normalForms (f : Monoid.End U) : Subgroup (Torus f) where
  carrier := {x | ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹}
  one_mem' := ⟨0,0,1,by simp⟩
  inv_mem' := by
    rintro x ⟨p,q,u,rfl⟩
    exact ⟨q,p,u⁻¹,by simp only [mul_inv_rev, inv_inv, map_inv, mul_assoc]⟩
  mul_mem' := by
    rintro x y ⟨p,q,u,rfl⟩ ⟨r,s,v,rfl⟩
    refine ⟨p+r,q+s,(f^r) u * (f^q) v,?_⟩
    have ht : (stable f ^ q)⁻¹ * stable f ^ r =
        stable f ^ r * (stable f ^ q)⁻¹ := (Commute.pow_pow (Commute.refl (stable f)) q r).inv_left.eq
    calc
      _ = stable f ^ p * (of f u * stable f ^ r) *
          ((stable f ^ q)⁻¹ * of f v) * (stable f ^ s)⁻¹ := by
            simp only [mul_assoc]
            rw [← mul_assoc ((stable f ^ q)⁻¹),ht]
            simp only [mul_assoc]
      _ = _ := by
        rw [of_mul_stable_pow,inv_stable_pow_mul_of,map_mul,pow_add,pow_add,mul_inv_rev]
        have ht' : (stable f ^ s)⁻¹ * (stable f ^ q)⁻¹ =
            (stable f ^ q)⁻¹ * (stable f ^ s)⁻¹ :=
          (Commute.pow_pow (Commute.refl (stable f)) s q).inv_left.inv_right.eq
        rw [ht']
        simp only [mul_assoc]

lemma of_mem_normalForms (f : Monoid.End U) (u : U) : of f u ∈ normalForms f :=
  ⟨0,0,u,by simp⟩

lemma stable_mem_normalForms (f : Monoid.End U) : stable f ∈ normalForms f :=
  ⟨1,0,1,by simp⟩

theorem normal_form (f : Monoid.End U) (x : Torus f) :
    ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹ := by
  change x ∈ normalForms f
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (relations f) x
  induction w using Coprod.induction_on with
  | inl u => exact of_mem_normalForms f u
  | inr z =>
    have hz : inr z = (letter (U := U)) ^ toAdd z := by
      rw [letter,← map_zpow]
      congr 1
      change z = ofAdd ((toAdd z) • (1 : ℤ))
      simp
    rw [hz,map_zpow]
    exact (normalForms f).zpow_mem (stable_mem_normalForms f) _
  | mul x y hx hy =>
    rw [map_mul]
    exact (normalForms f).mul_mem hx hy

def height (f : Monoid.End U) : Torus f →* Multiplicative ℤ :=
  lift f 1 (ofAdd 1) (by intro u; simp)

@[simp] lemma height_of (f : Monoid.End U) (u : U) : height f (of f u) = 1 :=
  lift_of f 1 (ofAdd 1) _ u

@[simp] lemma height_stable (f : Monoid.End U) : height f (stable f) = ofAdd 1 :=
  lift_stable f 1 (ofAdd 1) _

end

section
open Monoid Multiplicative
universe u
variable {U : Type u} [Group U]

abbrev Coset (f : Monoid.End U) := Torus f ⧸ (of f).range

def coset (f : Monoid.End U) (x : Torus f) : Coset f := QuotientGroup.mk x

lemma coset_mul_of (f : Monoid.End U) (x : Torus f) (u : U) :
    coset f (x * of f u) = coset f x :=
  QuotientGroup.mk_mul_of_mem x ⟨u,rfl⟩

def next (f : Monoid.End U) : Coset f → Coset f :=
  Quotient.map' (fun x => x * stable f) (by
    intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    obtain ⟨u,hu⟩ := h
    refine ⟨f u,?_⟩
    rw [mul_inv_rev,mul_assoc,← mul_assoc x⁻¹,← hu]
    exact (inverse_conjugate f u).symm)

@[simp] lemma next_coset (f : Monoid.End U) (x : Torus f) :
    next f (coset f x) = coset f (x * stable f) := rfl

lemma next_iterate_coset (f : Monoid.End U) (k : ℕ) (x : Torus f) :
    (next f)^[k] (coset f x) = coset f (x * stable f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,next_coset,pow_succ,mul_assoc]

lemma reaches_base_ray (f : Monoid.End U) (c : Coset f) :
    ∃ (p q : ℕ), (next f)^[q] c = (next f)^[p] (coset f 1) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨p,q,u,hx⟩ := normal_form f x
  refine ⟨p,q,?_⟩
  change (next f)^[q] (coset f x) = _
  rw [next_iterate_coset,next_iterate_coset,hx,mul_assoc,
    inv_mul_cancel,mul_one,one_mul,coset_mul_of]

lemma common_descendant (f : Monoid.End U) (c d : Coset f) :
    ∃ (p q : ℕ), (next f)^[p] c = (next f)^[q] d := by
  obtain ⟨p,q,hc⟩ := reaches_base_ray f c
  obtain ⟨r,s,hd⟩ := reaches_base_ray f d
  refine ⟨r+q,p+s,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hc,hd,
    ← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm r p]

def cosetHeight (f : Monoid.End U) : Coset f → ℤ :=
  Quotient.lift (fun x => toAdd (height f x)) (by
    intro x y h
    have h' : x⁻¹ * y ∈ (of f).range := QuotientGroup.leftRel_apply.mp h
    obtain ⟨u,hu⟩ := h'
    have hy : y = x * of f u := by rw [hu,mul_inv_cancel_left]
    rw [hy,map_mul,height_of,mul_one])

@[simp] lemma cosetHeight_coset (f : Monoid.End U) (x : Torus f) :
    cosetHeight f (coset f x) = toAdd (height f x) := rfl

lemma height_next (f : Monoid.End U) (c : Coset f) :
    cosetHeight f (next f c) = cosetHeight f c + 1 := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    change cosetHeight f (next f (coset f x)) = cosetHeight f (coset f x) + 1
    rw [next_coset,cosetHeight_coset,cosetHeight_coset,map_mul,height_stable]
    rfl

noncomputable def origin (f : Monoid.End U) (c : Coset f) : Torus f := c.out

@[simp] lemma coset_origin (f : Monoid.End U) (c : Coset f) :
    coset f (origin f c) = c := Quotient.out_eq' c

lemma origin_next_mem (f : Monoid.End U) (c : Coset f) :
    (origin f (next f c))⁻¹ * (origin f c * stable f) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (next f c)) = coset f (origin f c * stable f)
  rw [coset_origin,← next_coset,coset_origin]

noncomputable def cosetOffset (f : Monoid.End U) (c : Coset f) : U :=
  Classical.choose (origin_next_mem f c)

lemma origin_next (f : Monoid.End U) (c : Coset f) :
    origin f (next f c) * of f (cosetOffset f c) = origin f c * stable f := by
  change origin f (next f c) * of f (Classical.choose (origin_next_mem f c)) = _
  rw [Classical.choose_spec (origin_next_mem f c),mul_inv_cancel_left]

end

open Monoid Multiplicative
noncomputable section
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

lemma smul_coset (g x : Torus f) : g • coset f x = coset f (g*x) := rfl
lemma next_smul (g : Torus f) (c : Coset f) : next f (g • c) = g • next f c := by
  induction c using QuotientGroup.induction_on with
  | H x => change coset f ((g*x)*stable f) = coset f (g*(x*stable f)); rw [mul_assoc]

lemma origin_action_mem (g : Torus f) (c : Coset f) :
    (origin f (g • c))⁻¹ * (g * origin f c) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (g • c)) = coset f (g * origin f c)
  rw [coset_origin,← smul_coset,coset_origin]

def actionOffset (g : Torus f) (c : Coset f) : U :=
  Classical.choose (origin_action_mem f g c)
lemma origin_action (g : Torus f) (c : Coset f) :
    origin f (g • c) * of f (actionOffset f g c) = g * origin f c := by
  rw [actionOffset,Classical.choose_spec (origin_action_mem f g c),mul_inv_cancel_left]

variable (hf : Function.Injective f)
include hf
lemma actionOffset_one (c : Coset f) : actionOffset f 1 c = 1 := by
  apply of_injective f hf
  have h := origin_action f 1 c
  rw [one_smul,one_mul] at h
  exact (mul_left_cancel (h.trans (mul_one _).symm)).trans (map_one _).symm
lemma actionOffset_mul (g h : Torus f) (c : Coset f) :
    actionOffset f (g*h) c = actionOffset f g (h • c) * actionOffset f h c := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f ((g*h) • c))
  rw [map_mul,origin_action,mul_smul,←mul_assoc,origin_action]
  rw [mul_assoc,mul_assoc,origin_action]
lemma actionOffset_next (g : Torus f) (c : Coset f) :
    actionOffset f g (next f c) * cosetOffset f c =
      cosetOffset f (g • c) * f (actionOffset f g c) := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f (next f (g • c)))
  calc
    origin f (next f (g • c)) * of f (actionOffset f g (next f c) * cosetOffset f c) =
        (origin f (g • next f c) * of f (actionOffset f g (next f c))) * of f (cosetOffset f c) := by rw [map_mul,←mul_assoc,next_smul]
    _ = g * (origin f (next f c) * of f (cosetOffset f c)) := by rw [origin_action,mul_assoc]
    _ = g * (origin f c * stable f) := by rw [origin_next]
    _ = (origin f (g • c) * of f (actionOffset f g c)) * stable f := by rw [origin_action,mul_assoc]
    _ = (origin f (g • c) * stable f) * of f (f (actionOffset f g c)) := by rw [mul_assoc,of_mul_stable,←mul_assoc]
    _ = (origin f (next f (g • c)) * of f (cosetOffset f (g • c))) * of f (f (actionOffset f g c)) := by rw [origin_next]
    _ = origin f (next f (g • c)) * of f (cosetOffset f (g • c) * f (actionOffset f g c)) := by rw [map_mul,mul_assoc]

end
end UniversalFInfinity.AscendingTorus

end OAI
