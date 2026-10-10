import Mathlib
import OAI.GroupTheory.FiniteType.StandardHomology

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace AscendingHNN
section

variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

def associatedEquiv : (⊤ : Subgroup U) ≃* f.range :=
  (Subgroup.topEquiv).trans (MonoidHom.ofInjective hf)

abbrev Torus := HNNExtension U ⊤ f.range (associatedEquiv f hf)

def embed : U →* Torus f hf := HNNExtension.of

def stable : Torus f hf := HNNExtension.t⁻¹

lemma embed_injective : Function.Injective (embed f hf) := HNNExtension.of_injective (associatedEquiv f hf)

lemma embed_mul_stable (u : U) :
    embed f hf u * stable f hf = stable f hf * embed f hf (f u) := by
  exact HNNExtension.of_mul_inv_t (⟨u,Subgroup.mem_top u⟩ : (⊤ : Subgroup U))

lemma embed_mul_stable_pow (u : U) (n : ℕ) :
    embed f hf u * (stable f hf)^n =
      (stable f hf)^n * embed f hf ((f : U → U)^[n] u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,← mul_assoc,ih,mul_assoc,embed_mul_stable,← mul_assoc,← pow_succ,
      Function.iterate_succ_apply']

lemma expand_normal (p q n : ℕ) (u : U) :
    (stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹ =
      (stable f hf)^(p+n) * embed f hf ((f : U → U)^[n] u) *
        ((stable f hf)^(q+n))⁻¹ := by
  calc
    _ = (stable f hf)^p * (embed f hf u * (stable f hf)^n) *
        ((stable f hf)^n)⁻¹ * ((stable f hf)^q)⁻¹ := by group
    _ = _ := by rw [embed_mul_stable_pow,pow_add,pow_add]; group

theorem normal_form (j : Torus f hf) :
    ∃ p q : ℕ, ∃ u : U, j = (stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹ := by
  induction j using HNNExtension.induction_on with
  | of u => exact ⟨0,0,u,by simp [embed]⟩
  | t => exact ⟨0,1,1,by simp [stable]⟩
  | mul x y hx hy =>
    obtain ⟨p,q,u,rfl⟩ := hx
    obtain ⟨r,s,v,rfl⟩ := hy
    refine ⟨p+r,s+q,((f : U → U)^[r] u)*((f : U → U)^[q] v),?_⟩
    conv_lhs => lhs; rw [expand_normal f hf p q r u]
    conv_lhs => rhs; rw [expand_normal f hf r s q v]
    rw [map_mul,show q+r=r+q by omega]
    group
  | inv x hx =>
    obtain ⟨p,q,u,rfl⟩ := hx
    refine ⟨q,p,u⁻¹,?_⟩
    rw [map_inv]
    group

def heightHom : Torus f hf →* Multiplicative ℤ :=
  HNNExtension.lift 1 (Multiplicative.ofAdd (-1)) (by intro a; simp)

def height (j : Torus f hf) : ℤ := Multiplicative.toAdd (heightHom f hf j)

@[simp] lemma height_mul (j k : Torus f hf) :
    height f hf (j*k) = height f hf j + height f hf k := by
  simp [height]

@[simp] lemma height_embed (u : U) : height f hf (embed f hf u) = 0 := by
  simp [height,heightHom,embed]

@[simp] lemma height_stable : height f hf (stable f hf) = 1 := by
  simp [height,heightHom,stable]

@[simp] lemma height_inv (j : Torus f hf) : height f hf j⁻¹ = -height f hf j := by
  simp [height]

abbrev Vertex := Torus f hf ⧸ (embed f hf).range

def parent : Vertex f hf → Vertex f hf :=
  Quotient.map' (fun j => j * stable f hf) (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    obtain ⟨u,hu⟩ := QuotientGroup.leftRel_apply.mp h
    refine ⟨f u,?_⟩
    have hc : (stable f hf)⁻¹ * embed f hf u * stable f hf = embed f hf (f u) := by
      rw [mul_assoc,embed_mul_stable]
      group
    rw [← hc,hu]
    group)

@[simp] lemma parent_mk (j : Torus f hf) :
    parent f hf (QuotientGroup.mk j) = QuotientGroup.mk (j * stable f hf) := rfl

lemma parent_iterate_mk (n : ℕ) (j : Torus f hf) :
    (parent f hf)^[n] (QuotientGroup.mk j) = QuotientGroup.mk (j * (stable f hf)^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply',ih,parent_mk,pow_succ,mul_assoc]

def vertexHeight : Vertex f hf → ℤ :=
  Quotient.lift (height f hf) (by
    intro a b h
    obtain ⟨u,hu⟩ := QuotientGroup.leftRel_apply.mp h
    have hh : height f hf (a⁻¹*b) = 0 := by rw [← hu,height_embed]
    simp only [height_mul,height_inv] at hh
    omega)

@[simp] lemma vertexHeight_mk (j : Torus f hf) :
    vertexHeight f hf (QuotientGroup.mk j) = height f hf j := rfl

lemma parent_raises (v : Vertex f hf) :
    vertexHeight f hf (parent f hf v) = vertexHeight f hf v + 1 := by
  induction v using Quotient.inductionOn
  simp

lemma forward_meets_base (v : Vertex f hf) :
    ∃ n m : ℕ, (parent f hf)^[n] v =
      (parent f hf)^[m] (QuotientGroup.mk (1 : Torus f hf)) := by
  induction v using Quotient.inductionOn with
  | h j =>
    obtain ⟨p,q,u,hj⟩ := normal_form f hf j
    refine ⟨q,p,?_⟩
    rw [parent_iterate_mk,parent_iterate_mk,one_mul,hj]
    have he : ((stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹) * (stable f hf)^q =
        (stable f hf)^p * embed f hf u := by group
    rw [he]
    exact QuotientGroup.mk_mul_of_mem _ ⟨u,rfl⟩

lemma forward_merge (v w : Vertex f hf) :
    ∃ n m : ℕ, (parent f hf)^[n] v = (parent f hf)^[m] w := by
  obtain ⟨n,m,hv⟩ := forward_meets_base f hf v
  obtain ⟨r,s,hw⟩ := forward_meets_base f hf w
  refine ⟨s+n,m+r,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hv,hw,
    ← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm s m]

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {U : Type} [Group U] (f : U →* U) (hf : Function.Injective f)

lemma parent_smul (j : Torus f hf) (v : Vertex f hf) :
    parent f hf (j • v) = j • parent f hf v := by
  induction v using Quotient.inductionOn with
  | h k =>
    simp only [MulAction.Quotient.smul_mk,smul_eq_mul,parent_mk,mul_assoc]

variable {R : Type} [CommRing R] (A : Rep R (Torus f hf))

abbrev treeComplex : ShortComplex (Rep R (Torus f hf)) :=
  FunctionalTree.equivariantComplex A (parent f hf) (parent_smul f hf)

theorem treeComplex_shortExact : (treeComplex f hf A).ShortExact := by
  let : Nonempty (Vertex f hf) := ⟨QuotientGroup.mk (1 : Torus f hf)⟩
  exact FunctionalTree.equivariantComplex_shortExact A (parent f hf) (parent_smul f hf)
    (forward_merge f hf) (vertexHeight f hf) (parent_raises f hf)

end AscendingHNN

namespace ListChains
variable {G H : Type} [Group G] [Group H]
variable {K : Type} [CommRing K] {f : G →* G}

def IdempotentSplittings.conjugate (F : IdempotentSplittings G K f) (e : G ≃* H) :
    IdempotentSplittings H K ((e.toMonoidHom.comp f).comp e.symm.toMonoidHom) where
  map E := (e.toMonoidHom.comp (F.map E)).comp e.symm.toMonoidHom
  identity := by rw [F.identity]
  commute E P hsum hEP hPE u v :=
    (F.commute E P hsum hEP hPE (e.symm u) (e.symm v)).map e.toMonoidHom
  addition E P hsum hEP hPE u := by
    change e (F.map ⟨_,hsum⟩ (e.symm u)) = _
    rw [F.addition E P hsum hEP hPE,map_mul]
    rfl

lemma uniformFillings_conjugate_of_factorization
    {P : Type} [Group P] [Group.FG P] (a : G →* P) (b : P →* G)
    (F₂ : IdempotentSplittings G (ZMod 2) (b.comp a))
    (F₃ : IdempotentSplittings G (ZMod 3) (b.comp a)) (e : G ≃* H) :
    ∀ n, UniformFillings H ((e.toMonoidHom.comp (b.comp a)).comp e.symm.toMonoidHom) n := by
  have h₂ : IdempotentSplittings H (ZMod 2)
      ((e.toMonoidHom.comp b).comp (a.comp e.symm.toMonoidHom)) := by
    simpa only [MonoidHom.comp_assoc] using F₂.conjugate e
  have h₃ : IdempotentSplittings H (ZMod 3)
      ((e.toMonoidHom.comp b).comp (a.comp e.symm.toMonoidHom)) := by
    simpa only [MonoidHom.comp_assoc] using F₃.conjugate e
  simpa only [MonoidHom.comp_assoc] using
    uniform_fillings_of_factorization_and_splittings H
      (a.comp e.symm.toMonoidHom) (e.toMonoidHom.comp b) h₂ h₃
end ListChains

namespace AscendingHNN
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {U P : Type} [Group U] [Group P] [Group.FG P]
variable (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))
variable (F₂ : ListChains.IdempotentSplittings U (ZMod 2) (b.comp a))
variable (F₃ : ListChains.IdempotentSplittings U (ZMod 3) (b.comp a))

abbrev baseEquiv : U ≃* (embed (b.comp a) hf).range :=
  MonoidHom.ofInjective (embed_injective (b.comp a) hf)

abbrev baseShift : (embed (b.comp a) hf).range →* (embed (b.comp a) hf).range :=
  ((baseEquiv a b hf).toMonoidHom.comp (b.comp a)).comp (baseEquiv a b hf).symm.toMonoidHom

omit [Group.FG P] in
lemma baseShift_relation (s : (embed (b.comp a) hf).range) :
    (s : Torus (b.comp a) hf) * stable (b.comp a) hf =
      stable (b.comp a) hf * (baseShift a b hf s : Torus (b.comp a) hf) := by
  have h := embed_mul_stable (b.comp a) hf ((baseEquiv a b hf).symm s)
  have he : embed (b.comp a) hf ((baseEquiv a b hf).symm s) = s :=
    congrArg Subtype.val ((baseEquiv a b hf).apply_symm_apply s)
  rw [he] at h
  exact h

include F₂ F₃ in

theorem regular_product_homology_vanishes (I : Type) (n : ℕ) :
    ∀ x : groupHomology (RegularProduct.rep (Torus (b.comp a) hf) I) (n+2), x=0 := by
  let S := (embed (b.comp a) hf).range
  let : Nonempty (Torus (b.comp a) hf ⧸ S) := ⟨QuotientGroup.mk (1 : Torus (b.comp a) hf)⟩
  have hfill := ListChains.uniformFillings_conjugate_of_factorization a b F₂ F₃ (baseEquiv a b hf)
  exact RegularProduct.vanishing (Torus (b.comp a) hf) I S (baseShift a b hf)
    (stable (b.comp a) hf) (baseShift_relation a b hf)
    (parent (b.comp a) hf) (parent_smul (b.comp a) hf)
    (by simpa only [one_mul] using parent_mk (b.comp a) hf 1)
    (hfill (n+1)) (hfill (n+2)) (forward_merge (b.comp a) hf)
    (vertexHeight (b.comp a) hf) (parent_raises (b.comp a) hf)

end

variable {U V : Type*} [Group U] [Group V]
variable (f : U →* U) (hf : Function.Injective f)

@[ext] lemma hom_ext {i j : Torus f hf →* V}
    (hi : ∀ u, i (embed f hf u)=j (embed f hf u))
    (ht : i (stable f hf)=j (stable f hf)) : i=j := by
  apply HNNExtension.hom_ext
  · ext u
    exact hi u
  · apply inv_injective
    exact (map_inv i _).symm.trans (ht.trans (map_inv j _))

variable (i : U →* V) (t : V) (ht : ∀ u, i u*t=t*i (f u))

include ht in
lemma inv_conjugation (u : U) : t⁻¹ * i u = i (f u) * t⁻¹ := by
  calc
    _ = t⁻¹*(i u*t)*t⁻¹ := by group
    _ = _ := by rw [ht]; group

def evaluation : Torus f hf →* V :=
  HNNExtension.lift i t⁻¹ (fun u => inv_conjugation f i t ht u)

@[simp] lemma evaluation_embed (u : U) : evaluation f hf i t ht (embed f hf u)=i u :=
  HNNExtension.lift_of _ _ _ u

@[simp] lemma evaluation_stable : evaluation f hf i t ht (stable f hf)=t := by
  change (HNNExtension.lift i t⁻¹ (fun u : (⊤ : Subgroup U) => inv_conjugation f i t ht u))
    HNNExtension.t⁻¹ = t
  rw [map_inv]
  exact (congrArg Inv.inv (HNNExtension.lift_t _ _ _)).trans (inv_inv t)

lemma evaluation_normal (a b : ℕ) (u : U) :
    evaluation f hf i t ht ((stable f hf)^a * embed f hf u * ((stable f hf)^b)⁻¹) =
      t^a * i u * (t^b)⁻¹ := by
  simp only [map_mul,map_inv,map_pow,evaluation_embed,evaluation_stable]

lemma evaluation_injective (hi : Function.Injective i) (β : V →* Multiplicative ℤ)
    (hβi : ∀ u, β (i u)=1) (hβt : β t=Multiplicative.ofAdd 1) :
    Function.Injective (evaluation f hf i t ht) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a,b,u,rfl⟩ := normal_form f hf g
  rw [evaluation_normal] at hg
  have hb := congrArg (fun v => Multiplicative.toAdd (β v)) hg
  simp only [map_mul,map_pow,map_inv,hβi,hβt,mul_one,map_one] at hb
  have hab : a=b := by
    simp only [toAdd_mul,toAdd_pow,
      toAdd_inv,toAdd_ofAdd,toAdd_one,
      nsmul_eq_mul,mul_one] at hb
    omega
  subst b
  have hu : u=1 := hi (by
    apply mul_left_cancel (a := t^a)
    apply mul_right_cancel (b := (t^a)⁻¹)
    simpa only [map_one,mul_one,mul_inv_cancel] using hg)
  simp [hu]

lemma evaluation_surjective
    (h : ∀ v : V, ∃ a b : ℕ, ∃ u, v=t^a*i u*(t^b)⁻¹) :
    Function.Surjective (evaluation f hf i t ht) := by
  intro v
  obtain ⟨a,b,u,rfl⟩ := h v
  exact ⟨(stable f hf)^a*embed f hf u*((stable f hf)^b)⁻¹,evaluation_normal f hf i t ht a b u⟩

end AscendingHNN

end

end OAI
