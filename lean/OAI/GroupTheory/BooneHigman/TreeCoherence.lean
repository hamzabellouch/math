import OAI.GroupTheory.BooneHigman.BinaryCoherence
import OAI.GroupTheory.BooneHigman.EndpointCoherence

namespace OAI

noncomputable section

/-!
Decorated tree interpretation, grafting, leaf values, and common-refinement invariance.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

section
universe v
open BinaryGroupCategory
variable {X : Type v}

/-- Number of internal nodes, so that the number of leaves is `arity+1`. -/
abbrev arity : Tree X → ℕ
  | .leaf => 0
  | .split _ a b => arity a+arity b+1

/-- Left-to-right exact ordinal enumeration of the leaves. -/
def ordinal : (a : Tree X) → a.Leaves ≃ Fin (a.arity+1)
  | .leaf => {
      toFun := fun _=>0
      invFun := fun _=>PUnit.unit
      left_inv := by rintro ⟨⟩; rfl
      right_inv := by intro i; apply Fin.ext; have hi := i.isLt; change (i:ℕ)<1 at hi; change 0=(i:ℕ); omega }
  | .split _ a b => (Equiv.sumCongr (ordinal a) (ordinal b)).trans (sumIndex a.arity b.arity)

@[simp] lemma ordinal_leaf (i : (.leaf : Tree X).Leaves) : ordinal .leaf i=0 := rfl
@[simp] lemma ordinal_left (x:X) (a b:Tree X) (i:a.Leaves) :
    ordinal (.split x a b) (Sum.inl i)=sumIndex a.arity b.arity (Sum.inl (ordinal a i)) := rfl
@[simp] lemma ordinal_right (x:X) (a b:Tree X) (i:b.Leaves) :
    ordinal (.split x a b) (Sum.inr i)=sumIndex a.arity b.arity (Sum.inr (ordinal b i)) := rfl

def ordinalEquiv {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Fin (a.arity+1) ≃ Fin (b.arity+1) :=
  (ordinal a).symm.trans (e.trans (ordinal b))

@[simp] lemma ordinalEquiv_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (i:a.Leaves) :
    ordinalEquiv e (ordinal a i)=ordinal b (e i) := by simp [ordinalEquiv]

lemma ordinalEquiv_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves) :
    ordinalEquiv (e.trans f)=(ordinalEquiv e).trans (ordinalEquiv f) := by
  apply Equiv.ext; intro i
  simp [ordinalEquiv]

lemma ordinalEquiv_sum {a b c e:Tree X} (x y:X) (f:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ e.Leaves) :
    ordinalEquiv (a:=.split x a b) (b:=.split y c e) (Equiv.sumCongr f g)=
      sumEquiv (ordinalEquiv f) (ordinalEquiv g) := by
  apply Equiv.ext; intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x a b)).surjective i
  cases j <;> simp only [ordinalEquiv,ordinal,Equiv.trans_apply,Equiv.sumCongr_symm,
    Equiv.symm_trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,sumEquiv_left,sumEquiv_right]

lemma ordinalEquiv_exchange {a b:Tree X} (x y:X) :
    ordinalEquiv (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)=
      exchangeEquiv a.arity b.arity := by
  apply Equiv.ext; intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x a b)).surjective i
  cases j <;> simp only [ordinalEquiv,ordinal,Equiv.trans_apply,Equiv.sumCongr_symm,
    Equiv.symm_trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    Equiv.sumComm_apply,Sum.swap_inl,Sum.swap_inr,exchangeEquiv_left,exchangeEquiv_right]

end

section
universe v w
open BinaryGroupCategory
variable {X : Type v} {H : Type w} [Group H] (d : Data H) (q : SymmetryData d) (B : X → H)

/-- Interpret the split tree as a map from its ordered comb of leaves. -/
def flatten : Tree X → H
  | .leaf => 1
  | .split x a b => B x*d.tensor (flatten a,flatten b)*(merge d a.arity)⁻¹

/-- The actual groupoid interpretation of a whole permutation of leaves. -/
def leafValue {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : H :=
  flatten d B b * equivVal d q (ordinalEquiv e) * (flatten d B a)⁻¹

lemma leafValue_refl (a:Tree X) : leafValue d q B (Equiv.refl a.Leaves)=1 := by
  have he : ordinalEquiv (Equiv.refl a.Leaves)=Equiv.refl (Fin (a.arity+1)) := by
    apply Equiv.ext; intro i; simp [ordinalEquiv]
  rw [leafValue,he,equivVal_refl,mul_one,mul_inv_cancel]

lemma leafValue_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves) :
    leafValue d q B (e.trans f)=leafValue d q B f*leafValue d q B e := by
  rw [leafValue,ordinalEquiv_trans,equivVal_trans]
  dsimp only [leafValue]
  group

lemma leafValue_symm {a b:Tree X} (e:a.Leaves ≃ b.Leaves) :
    leafValue d q B e.symm=(leafValue d q B e)⁻¹ := by
  have hh := leafValue_trans d q B e e.symm
  rw [Equiv.self_trans_symm,leafValue_refl] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

lemma leafValue_sum {a b c e:Tree X} (x y:X) (f:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ e.Leaves) :
    leafValue d q B (a:=.split x a b) (b:=.split y c e) (Equiv.sumCongr f g)=
      B y*d.tensor (leafValue d q B f,leafValue d q B g)*(B x)⁻¹ := by
  rw [leafValue,ordinalEquiv_sum,equivVal_sum]
  dsimp only [flatten,leafValue,blockMap]
  have ht : d.tensor (flatten d B c * equivVal d q (ordinalEquiv f) * (flatten d B a)⁻¹,
      flatten d B e * equivVal d q (ordinalEquiv g) * (flatten d B b)⁻¹)=
      d.tensor (flatten d B c,flatten d B e)*
        d.tensor (equivVal d q (ordinalEquiv f),equivVal d q (ordinalEquiv g))*
          (d.tensor (flatten d B a,flatten d B b))⁻¹ := by
    rw [← map_inv,← map_mul,← map_mul]; rfl
  rw [ht]; group

lemma leafValue_exchange {a b:Tree X} (x y:X) :
    leafValue d q B (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)=
      B y*q.c*(B x)⁻¹ := by
  rw [leafValue,ordinalEquiv_exchange,equivVal_exchange]
  dsimp only [flatten]
  have hn := q.naturality (flatten d B a) (flatten d B b)
  calc
    _=B y*d.tensor (flatten d B b,flatten d B a)*q.c*
        (d.tensor (flatten d B a,flatten d B b))⁻¹*(B x)⁻¹ := by group
    _=_ := by rw [← hn]; group

lemma equivVal_ordinal_assoc (x y z w:X) (a b c:Tree X) :
    equivVal d q (ordinalEquiv (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _))=1 := by
  apply equivVal_order
  intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x (.split y a b) c)).surjective i
  rw [ordinalEquiv_apply]
  rcases j with (j|j)|j <;>
    simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,
      Equiv.sumAssoc_apply_inr,ordinal,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      sumIndex_left_val,sumIndex_right_val,arity]
  omega

lemma flatten_assoc (x y z w:X) (a b c:Tree X) :
    flatten d B (.split z a (.split w b c)) =
      (B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹)*
        flatten d B (.split x (.split y a b) c) := by
  let fa := flatten d B a
  let fb := flatten d B b
  let fc := flatten d B c
  have hT (l m n r:H) : d.tensor (l*m,n*r)=d.tensor (l,n)*d.tensor (m,r) :=
    d.tensor.map_mul (l,n) (m,r)
  have hR : d.tensor (fa,B w*d.tensor (fb,fc)*(merge d b.arity)⁻¹)=
      d.tensor (1,B w)*d.tensor (fa,d.tensor (fb,fc))*(right d (merge d b.arity))⁻¹ := by
    dsimp only [right,left,MonoidHom.coe_mk,OneHom.coe_mk]
    rw [← map_inv,← map_mul,← map_mul]
    simp only [Prod.inv_mk,Prod.mk_mul_mk,inv_one,one_mul,mul_one]
  have hL : d.tensor (B y*d.tensor (fa,fb)*(merge d a.arity)⁻¹,fc)=
      d.tensor (B y,1)*d.tensor (d.tensor (fa,fb),fc)*(left d (merge d a.arity))⁻¹ := by
    dsimp only [right,left,MonoidHom.coe_mk,OneHom.coe_mk]
    rw [← map_inv,← map_mul,← map_mul]
    simp only [Prod.inv_mk,Prod.mk_mul_mk,inv_one,one_mul,mul_one]
  change B z*d.tensor (fa,B w*d.tensor (fb,fc)*(merge d b.arity)⁻¹)*(merge d a.arity)⁻¹ =
    (B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹)*
      (B x*d.tensor (B y*d.tensor (fa,fb)*(merge d a.arity)⁻¹,fc)*
        (merge d (a.arity+b.arity+1))⁻¹)
  rw [hR,hL,← d.naturality fa fb fc]
  have hm := merge_coherence d a.arity b.arity
  calc
    _ = B z*d.tensor (1,B w)*d.tensor (fa,d.tensor (fb,fc))*
      d.a⁻¹*(merge d a.arity*right d (merge d b.arity)*d.a⁻¹)⁻¹ := by group
    _ = _ := by rw [← hm]; group

lemma leafValue_assoc (x y z w:X) (a b c:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _)=
      B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹ := by
  rw [leafValue,equivVal_ordinal_assoc,mul_one,flatten_assoc d B x y z w a b c]
  group

end

section
universe v
open BinaryGroupCategory
variable {X : Type v}

/-- Structural routes made only from tensor, associativity and exchange.
The arbitrary-permutation completeness theorem below is proved, not a constructor. -/
inductive Route : {a b:Tree X} → (a.Leaves ≃ b.Leaves) → Prop
  | refl (a) : Route (a:=a) (b:=a) (Equiv.refl _)
  | trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves} :
      Route e → Route f → Route (e.trans f)
  | symm {a b:Tree X} {e:a.Leaves ≃ b.Leaves} : Route e → Route e.symm
  | sum {a b c d:Tree X} (x y) {e:a.Leaves ≃ c.Leaves} {f:b.Leaves ≃ d.Leaves} :
      Route e → Route f → Route (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f)
  | assoc (x y z w) (a b c) : Route (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _)
  | exchange (x y) (a b) : Route (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)

def Ordered {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Prop :=
  ∀ i,(ordinal b (e i):ℕ)=ordinal a i

lemma Ordered.trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves}
    (he:Ordered e) (hf:Ordered f) : Ordered (e.trans f) := fun i=>(hf (e i)).trans (he i)
lemma Ordered.symm {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (he:Ordered e) : Ordered e.symm := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm
lemma Ordered.unique {a b:Tree X} {e f:a.Leaves ≃ b.Leaves} (he:Ordered e) (hf:Ordered f) : e=f := by
  apply Equiv.ext; intro i
  apply (ordinal b).injective
  exact Fin.ext ((he i).trans (hf i).symm)

lemma Ordered.arity {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (_he:Ordered e) : a.arity=b.arity :=
  equiv_size (ordinalEquiv e)

lemma Ordered.sum {a b c d:Tree X} (x y:X) {e:a.Leaves ≃ c.Leaves} {f:b.Leaves ≃ d.Leaves}
    (he:Ordered e) (hf:Ordered f) :
    Ordered (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) := by
  rintro (i|i) <;> simp only [ordinal,Equiv.sumCongr_apply,Equiv.trans_apply,Sum.map_inl,Sum.map_inr,
    sumIndex_left_val,sumIndex_right_val]
  · exact he i
  · rw [hf i,he.arity]

lemma ordered_assoc (x y z w:X) (a b c:Tree X) :
    Ordered (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) := by
  rintro ((i|i)|i) <;> simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,
    Equiv.sumAssoc_apply_inr,ordinal,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    sumIndex_left_val,sumIndex_right_val,arity]
  omega

abbrev comb (x:X) : ℕ → Tree X
  | 0 => .leaf
  | n+1 => .split x .leaf (comb x n)

@[simp] lemma arity_comb (x:X) (n:ℕ) : (comb x n).arity=n := by
  induction n with
  | zero => rfl
  | succ n ih => change 0+(comb x n).arity+1=n+1; rw [ih,Nat.zero_add]

lemma route_merge (x:X) (m n:ℕ) :
    ∃ e:(Tree.split x (comb x m) (comb x n)).Leaves ≃ (comb x (m+n+1)).Leaves,
      Route e ∧ Ordered e := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨Equiv.refl _,Route.refl _,fun _=>rfl⟩
  | succ m ih =>
    obtain ⟨e,he,hoe⟩ := ih
    have h : ∃ f:(Tree.split x (.split x .leaf (comb x m)) (comb x n)).Leaves ≃
        (Tree.split x .leaf (comb x (m+n+1))).Leaves,Route f ∧ Ordered f := by
      refine ⟨(Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) e),
        (Route.assoc x x x x .leaf _ _).trans (Route.sum x x (Route.refl .leaf) he),?_⟩
      exact (ordered_assoc x x x x .leaf _ _).trans (Ordered.sum x x (fun _=>rfl) hoe)
    rw [show (m+1)+n+1=(m+n+1)+1 by omega]
    exact h

lemma route_normal (x:X) (a:Tree X) :
    ∃ e:a.Leaves ≃ (comb x a.arity).Leaves,Route e ∧ Ordered e := by
  induction a with
  | leaf => exact ⟨Equiv.refl _,Route.refl _,fun _=>rfl⟩
  | split y a b ha hb =>
    obtain ⟨ea,hea,hoa⟩ := ha
    obtain ⟨eb,heb,hob⟩ := hb
    obtain ⟨em,hem,hom⟩ := route_merge x a.arity b.arity
    exact ⟨(Equiv.sumCongr ea eb).trans em,
      (Route.sum y x hea heb).trans hem,(Ordered.sum y x hoa hob).trans hom⟩

def combIndex (x:X) (n:ℕ) : (comb x n).Leaves ≃ Fin (n+1) :=
  (ordinal (comb x n)).trans (finCongr (congrArg (fun k=>k+1) (arity_comb x n)))

@[simp] lemma combIndex_left (x:X) (n:ℕ) (i:PUnit) :
    (combIndex x (n+1) (Sum.inl i):ℕ)=0 := rfl
@[simp] lemma combIndex_right (x:X) (n:ℕ) (i:(comb x n).Leaves) :
    (combIndex x (n+1) (Sum.inr i):ℕ)=1+(combIndex x n i:ℕ) := rfl

/-- Conjugate an ordinal permutation to the exact leaves of the comb. -/
def combPerm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) : Equiv.Perm (comb x n).Leaves :=
  (combIndex x n).trans (p.trans (combIndex x n).symm)

@[simp] lemma combIndex_perm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) (i:(comb x n).Leaves) :
    combIndex x n (combPerm x n p i)=p (combIndex x n i) := by simp [combPerm]

lemma combPerm_one (x:X) (n:ℕ) : combPerm x n 1=Equiv.refl _ := by
  apply Equiv.ext; intro i; simp [combPerm]
lemma combPerm_mul (x:X) (n:ℕ) (p r:Equiv.Perm (Fin (n+1))) :
    combPerm x n (p*r)=(combPerm x n r).trans (combPerm x n p) := by
  apply Equiv.ext; intro i; simp [combPerm]

lemma route_comb_adjacent (x:X) (n:ℕ) (i:Fin n) :
    Route (a:=comb x n) (b:=comb x n) (combPerm x n (Equiv.swap i.castSucc i.succ)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i=>?_) i
    · cases n with
      | zero =>
        have he : combPerm x 1 (Equiv.swap (0:Fin 1).castSucc (0:Fin 1).succ)=Equiv.sumComm PUnit PUnit := by
          apply Equiv.ext; intro j
          apply (combIndex x 1).injective
          apply Fin.ext
          rw [combIndex_perm]
          rcases j with ⟨⟩|⟨⟩ <;> rfl
        rw [he]
        exact Route.exchange x x .leaf .leaf
      | succ n =>
        let e : Equiv.Perm (comb x (n+2)).Leaves :=
          (Equiv.sumAssoc PUnit PUnit (comb x n).Leaves).symm.trans
            ((Equiv.sumCongr (Equiv.sumComm PUnit PUnit) (Equiv.refl _)).trans
              (Equiv.sumAssoc PUnit PUnit (comb x n).Leaves))
        have he : combPerm x (n+2) (Equiv.swap (0:Fin (n+2)).castSucc (0:Fin (n+2)).succ)=e := by
          apply Equiv.ext; intro j
          apply (combIndex x (n+2)).injective
          apply Fin.ext
          rw [combIndex_perm]
          rcases j with ⟨⟩|(⟨⟩|j)
          · rfl
          · rfl
          · have hj : combIndex x (n+2) (Sum.inr (Sum.inr j)) ≠ (0:Fin (n+2)).castSucc := by
              intro h; have h' := congrArg Fin.val h
              change 1+(1+(combIndex x n j:ℕ))=0 at h'; omega
            have hj' : combIndex x (n+2) (Sum.inr (Sum.inr j)) ≠ (0:Fin (n+2)).succ := by
              intro h; have h' := congrArg Fin.val h
              change 1+(1+(combIndex x n j:ℕ))=1 at h'; omega
            rw [Equiv.swap_apply_of_ne_of_ne hj hj']
            rfl
        rw [he]
        exact (Route.assoc x x x x .leaf .leaf (comb x n)).symm.trans
          ((Route.sum x x (Route.exchange x x .leaf .leaf) (Route.refl (comb x n))).trans
            (Route.assoc x x x x .leaf .leaf (comb x n)))
    · let e := Equiv.sumCongr (Equiv.refl PUnit) (combPerm x n (Equiv.swap i.castSucc i.succ))
      have he : combPerm x (n+1) (Equiv.swap i.succ.castSucc i.succ.succ)=e := by
        apply Equiv.ext; intro j
        apply (combIndex x (n+1)).injective
        apply Fin.ext
        rw [combIndex_perm]
        rcases j with ⟨⟩|j
        · have h₁ : combIndex x (n+1) (Sum.inl PUnit.unit) ≠ i.succ.castSucc := by
            intro h; have h' := congrArg Fin.val h
            change 0=(i:ℕ)+1 at h'; omega
          have h₂ : combIndex x (n+1) (Sum.inl PUnit.unit) ≠ i.succ.succ := by
            intro h; have h' := congrArg Fin.val h
            change 0=(i:ℕ)+1+1 at h'; omega
          rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]; rfl
        · change (Equiv.swap i.succ.castSucc i.succ.succ
              (combIndex x (n+1) (Sum.inr j)):ℕ)=
            1+(combIndex x n (combPerm x n (Equiv.swap i.castSucc i.succ) j):ℕ)
          rw [combIndex_perm]
          have h₁ (k:Fin (n+1)) :
              combIndex x (n+1) (Sum.inr j)=k.succ ↔ combIndex x n j=k := by
            constructor <;> intro h
            · apply Fin.ext; have hh := congrArg Fin.val h
              change 1+(combIndex x n j:ℕ)=(k:ℕ)+1 at hh; omega
            · apply Fin.ext; change 1+(combIndex x n j:ℕ)=(k:ℕ)+1; rw [h]; omega
          have hc : i.succ.castSucc=i.castSucc.succ := rfl
          rw [hc]
          simp only [Equiv.swap_apply_def,h₁]
          split_ifs
          · simp only [Fin.val_succ]; omega
          · simp only [Fin.val_succ]; omega
          · exact combIndex_right x n j
      rw [he]
      exact Route.sum x x (Route.refl .leaf) (ih i)

lemma route_comb_perm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) :
    Route (a:=comb x n) (b:=comb x n) (combPerm x n p) := by
  induction p using Adjacent.permutation_induction with
  | hone => rw [combPerm_one]; exact Route.refl _
  | hswap i => exact route_comb_adjacent x n i
  | hmul p r hp hr => rw [combPerm_mul]; exact hr.trans hp

lemma route_comb_equiv (x:X) (m n:ℕ) (e:(comb x m).Leaves ≃ (comb x n).Leaves) :
    Route e := by
  have h := equiv_size (((combIndex x m).symm.trans e).trans (combIndex x n))
  subst n
  let p : Equiv.Perm (Fin (m+1)) := (combIndex x m).symm.trans (e.trans (combIndex x m))
  have hp : combPerm x m p=e := by
    apply Equiv.ext; intro j; simp [combPerm,p]
  rw [← hp]
  exact route_comb_perm x m p

/-- Every bijection of leaves is generated by associativity, symmetries and tensor.
This is a finite-permutation coherence theorem, not an extra relation. -/
lemma route_complete (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Route e := by
  obtain ⟨ea,hea,_⟩ := route_normal x a
  obtain ⟨eb,heb,_⟩ := route_normal x b
  have h := hea.trans ((route_comb_equiv x a.arity b.arity (ea.symm.trans (e.trans eb))).trans heb.symm)
  have he : ea.trans ((ea.symm.trans (e.trans eb)).trans eb.symm)=e := by
    apply Equiv.ext; intro i; simp
  rw [he] at h
  exact h

end

section
universe v w
open BinaryGroupCategory
variable {X : Type v}

/-- Replace each leaf by the tree attached to its image. This is cabling of a
bijection, defined on the actual dependent leaf sets. -/
def graftLift {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) :
    (a.graft (fun i=>F (e i))).Leaves ≃ (b.graft F).Leaves :=
  (a.graftLeaves (fun i=>F (e i))).trans
    ((Equiv.sigmaCongr e (fun _=>Equiv.refl _)).trans (b.graftLeaves F).symm)

lemma graftLift_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X)
    (i:a.Leaves) (j:(F (e i)).Leaves) :
    graftLift e F ((a.graftLeaves (fun i=>F (e i))).symm ⟨i,j⟩)=
      (b.graftLeaves F).symm ⟨e i,j⟩ := by
  simp [graftLift,Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft]

lemma graftLift_refl (a:Tree X) (F:a.Leaves → Tree X) :
    graftLift (Equiv.refl a.Leaves) F=Equiv.refl (a.graft F).Leaves := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves F).symm.surjective j
  erw [graftLift_apply]; rfl

lemma graftLift_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves)
    (F:c.Leaves → Tree X) :
    graftLift (e.trans f) F=(graftLift e (fun i=>F (f i))).trans (graftLift f F) := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (f (e i)))).symm.surjective j
  calc
    _ = (c.graftLeaves F).symm ⟨f (e i),k⟩ := graftLift_apply (e.trans f) F i k
    _ = graftLift f F ((b.graftLeaves (fun i=>F (f i))).symm ⟨e i,k⟩) :=
      (graftLift_apply f F (e i) k).symm
    _ = _ := congrArg (graftLift f F) (graftLift_apply e (fun i=>F (f i)) i k).symm

lemma graftLift_sum {a b c d:Tree X} (x y:X) (e:a.Leaves ≃ c.Leaves) (f:b.Leaves ≃ d.Leaves)
    (F:(Tree.split y c d).Leaves → Tree X) :
    graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F =
      Equiv.sumCongr (graftLift e (fun i=>F (Sum.inl i))) (graftLift f (fun i=>F (Sum.inr i))) := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl (e i)))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F
      (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumCongr e f) i))).symm ⟨Sum.inl i,k⟩)=_
    erw [graftLift_apply]
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr (f i)))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F
      (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumCongr e f) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]

lemma graftLift_assoc (x y z w:X) (a b c:Tree X)
    (F:(Tree.split z a (.split w b c)).Leaves → Tree X) :
    graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c))
      (Equiv.sumAssoc _ _ _) F=Equiv.sumAssoc _ _ _ := by
  apply Equiv.ext
  rintro ((j|j)|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inl (Sum.inl i),k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr (Sum.inl i)))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inl (Sum.inr i),k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (c.graftLeaves (fun i=>F (Sum.inr (Sum.inr i)))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]; rfl

lemma graftLift_exchange (x y:X) (a b:Tree X)
    (F:(Tree.split y b a).Leaves → Tree X) :
    graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F=Equiv.sumComm _ _ := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inr i))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumComm _ _) i))).symm ⟨Sum.inl i,k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumComm _ _) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]; rfl

end

universe v w
open BinaryGroupCategory
variable {X : Type v} {H : Type w} [Group H] (d:Data H) (q:SymmetryData d) (B:X → H)

def cableValue {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) : H :=
  leafValue d q B (graftLift e F)

lemma cableValue_refl (a:Tree X) (F:a.Leaves → Tree X) :
    cableValue d q B (Equiv.refl a.Leaves) F=1 := by
  unfold cableValue
  rw [graftLift_refl]
  exact leafValue_refl d q B (a.graft F)

lemma cableValue_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves)
    (F:c.Leaves → Tree X) :
    cableValue d q B (e.trans f) F=
      cableValue d q B f F*cableValue d q B e (fun i=>F (f i)) := by
  unfold cableValue
  rw [graftLift_trans]
  exact leafValue_trans d q B (graftLift e (fun i=>F (f i))) (graftLift f F)

lemma cableValue_sum {a b c f:Tree X} (x y:X) (e:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ f.Leaves)
    (F:(Tree.split y c f).Leaves → Tree X) :
    cableValue d q B (a:=.split x a b) (b:=.split y c f) (Equiv.sumCongr e g) F=
      B y*d.tensor (cableValue d q B e (fun i=>F (Sum.inl i)),
        cableValue d q B g (fun i=>F (Sum.inr i)))*(B x)⁻¹ := by
  unfold cableValue
  rw [graftLift_sum]
  exact leafValue_sum d q B x y (graftLift e (fun i=>F (Sum.inl i)))
    (graftLift g (fun i=>F (Sum.inr i)))

lemma cableValue_assoc (x y z w:X) (a b c:Tree X)
    (F:(Tree.split z a (.split w b c)).Leaves → Tree X) :
    cableValue d q B (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c))
      (Equiv.sumAssoc _ _ _) F=B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹ := by
  unfold cableValue
  rw [graftLift_assoc]
  exact leafValue_assoc d q B x y z w (a.graft (fun i=>F (Sum.inl i)))
    (b.graft (fun i=>F (Sum.inr (Sum.inl i)))) (c.graft (fun i=>F (Sum.inr (Sum.inr i))))

lemma cableValue_exchange (x y:X) (a b:Tree X)
    (F:(Tree.split y b a).Leaves → Tree X) :
    cableValue d q B (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F=B y*q.c*(B x)⁻¹ := by
  unfold cableValue
  rw [graftLift_exchange]
  exact leafValue_exchange d q B x y

/-- Structural routes are invariant under replacing their wires by arbitrary
(nonempty) trees. This is cabling coherence for whole leaf permutations. -/
lemma Route.cableValue_eq {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (h:Route e)
    (F:b.Leaves → Tree X) : cableValue d q B e F=leafValue d q B e := by
  induction h with
  | refl a => rw [cableValue_refl,leafValue_refl]
  | @trans a b c e f he hf ihe ihf =>
    rw [cableValue_trans,ihe,ihf,leafValue_trans]
  | @symm a b e he ih =>
    have hh := cableValue_trans d q B e e.symm F
    rw [Equiv.self_trans_symm,cableValue_refl,ih] at hh
    rw [leafValue_symm]
    exact eq_inv_of_mul_eq_one_left hh.symm
  | @sum a b c f x y e g he hg ihe ihg =>
    rw [cableValue_sum,ihe,ihg,leafValue_sum]
  | assoc x y z w a b c => rw [cableValue_assoc,leafValue_assoc]
  | exchange x y a b => rw [cableValue_exchange,leafValue_exchange]

lemma leafValue_graftLift (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) :
    leafValue d q B (graftLift e F)=leafValue d q B e :=
  (route_complete x e).cableValue_eq d q B F

abbrev quad (x y:X) : Tree X := .split x (.split y .leaf .leaf) (.split y .leaf .leaf)

lemma flatten_bit (x:X) : flatten d B (.split x .leaf .leaf)=B x := by
  have ht : d.tensor (1,1)=1 := d.tensor.map_one
  simp only [flatten,arity,merge_zero,ht,mul_one,inv_one]
lemma flatten_quad (x y:X) : flatten d B (quad x y)=B x*d.tensor (B y,B y)*d.a := by
  change B x*d.tensor (flatten d B (.split y .leaf .leaf),flatten d B (.split y .leaf .leaf))*
    (merge d 1)⁻¹=_
  rw [flatten_bit,merge_succ,merge_zero,map_one,one_mul,inv_inv]

lemma ordinalEquiv_quad (x y z w:X) :
    ordinalEquiv (a:=quad x y) (b:=quad z w) (Equiv.sumSumSumComm PUnit PUnit PUnit PUnit)=
      Equiv.swap (1:Fin 4) (2:Fin 4) := by
  apply Equiv.ext; intro i
  fin_cases i <;> rfl

lemma leafValue_quad_middle (x y z w:X) :
    leafValue d q B (a:=quad x y) (b:=quad z w) (Equiv.sumSumSumComm PUnit PUnit PUnit PUnit)=
      (B z*d.tensor (B w,B w))*middleSwap d q*(B x*d.tensor (B y,B y))⁻¹ := by
  rw [leafValue,ordinalEquiv_quad,equivVal_same,flatten_quad,flatten_quad]
  change (B z*d.tensor (B w,B w)*d.a)*
    combPermutation d q 3 (Equiv.swap (1:Fin 3).castSucc (1:Fin 3).succ)*
      (B x*d.tensor (B y,B y)*d.a)⁻¹=_
  rw [combPermutation_swap,combSwap_internal d q (by decide)]
  change (B z*d.tensor (B w,B w)*d.a)*
    d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*(B x*d.tensor (B y,B y)*d.a)⁻¹=_
  dsimp only [middleSwap]
  group

lemma leafValue_middle (x y z w:X) (a b c f:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) (.split y c f))
      (b:=.split z (.split w a c) (.split w b f)) (Equiv.sumSumSumComm _ _ _ _)=
      (B z*d.tensor (B w,B w))*middleSwap d q*(B x*d.tensor (B y,B y))⁻¹ := by
  let F : (quad z w).Leaves → Tree X
    | Sum.inl (Sum.inl _) => a
    | Sum.inl (Sum.inr _) => c
    | Sum.inr (Sum.inl _) => b
    | Sum.inr (Sum.inr _) => f
  let e : (quad x y).Leaves ≃ (quad z w).Leaves := Equiv.sumSumSumComm _ _ _ _
  have he : graftLift e F=Equiv.sumSumSumComm a.Leaves b.Leaves c.Leaves f.Leaves := by
    apply Equiv.ext
    rintro ((i|i)|(i|i)) <;> rfl
  have hv := leafValue_graftLift d q B x e F
  rw [he] at hv
  exact hv.trans (leafValue_quad_middle d q B x y z w)

/-- The only additional colour relation needed for all tree-partition coherence. -/
structure GridLaw : Prop where
  grid : ∀ x y:X,x≠y → B x*d.tensor (B y,B y)=B y*d.tensor (B x,B x)*middleSwap d q

lemma leafValue_interchange (g:GridLaw d q B) {x y:X} (hxy:x≠y) (a b c f:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) (.split y c f))
      (b:=.split y (.split x a c) (.split x b f)) (Equiv.sumSumSumComm _ _ _ _)=1 := by
  rw [leafValue_middle,← g.grid x y hxy,mul_inv_cancel]

def SameBricks {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Prop :=
  ∀ i,a.brick i=b.brick (e i)

lemma SameBricks.unique {a b:Tree X} {e f:a.Leaves ≃ b.Leaves}
    (he:SameBricks e) (hf:SameBricks f) : e=f := by
  apply Equiv.ext; intro i
  exact b.partition.brick_injective ((he i).symm.trans (hf i))

lemma SameBricks.symm {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (he:SameBricks e) : SameBricks e.symm := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm
lemma SameBricks.trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves}
    (he:SameBricks e) (hf:SameBricks f) : SameBricks (e.trans f) :=
  fun i=>(he i).trans (hf (e i))

lemma SameBricks.brickSet_eq {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (he:SameBricks e) :
    a.brickSet=b.brickSet := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨e i,(he i).symm⟩
  · rintro ⟨i,rfl⟩; exact ⟨e.symm i,by simpa using he (e.symm i)⟩

lemma sameBricks_sum {a b c f:Tree X} (x:X) {e:a.Leaves ≃ c.Leaves} {g:b.Leaves ≃ f.Leaves}
    (he:SameBricks e) (hg:SameBricks g) :
    SameBricks (a:=.split x a b) (b:=.split x c f) (Equiv.sumCongr e g) := by
  rintro (i|i)
  · exact congrArg ((Prefix.oneBit x false).comp) (he i)
  · exact congrArg ((Prefix.oneBit x true).comp) (hg i)

lemma sameBricks_interchange {x y:X} (hxy:x≠y) (a b c f:Tree X) :
    SameBricks (a:=.split x (.split y a b) (.split y c f))
      (b:=.split y (.split x a c) (.split x b f)) (Equiv.sumSumSumComm _ _ _ _) := by
  rintro ((i|i)|(i|i)) <;>
    change (Prefix.oneBit x _).comp ((Prefix.oneBit y _).comp _) =
      (Prefix.oneBit y _).comp ((Prefix.oneBit x _).comp _) <;>
    rw [← Prefix.comp_assoc,← Prefix.comp_assoc,Prefix.oneBit_comp_comm hxy] <;> rfl

lemma Coherent.exists_value_one (g:GridLaw d q B) {a b:Tree X} (h:Coherent a b) :
    ∃ e:a.Leaves ≃ b.Leaves,SameBricks e ∧ leafValue d q B e=1 := by
  induction h with
  | refl a => exact ⟨Equiv.refl _,fun _=>rfl,leafValue_refl d q B a⟩
  | symm h ih =>
    obtain ⟨e,he,hv⟩ := ih
    exact ⟨e.symm,he.symm,by rw [leafValue_symm,hv,inv_one]⟩
  | trans h k ih ik =>
    obtain ⟨e,he,hv⟩ := ih
    obtain ⟨f,hf,hw⟩ := ik
    exact ⟨e.trans f,he.trans hf,by rw [leafValue_trans,hv,hw,mul_one]⟩
  | split x h k ih ik =>
    obtain ⟨e,he,hv⟩ := ih
    obtain ⟨f,hf,hw⟩ := ik
    refine ⟨Equiv.sumCongr e f,sameBricks_sum x he hf,?_⟩
    rw [leafValue_sum,hv,hw]
    have ht : d.tensor (1,1)=1 := d.tensor.map_one
    rw [ht,mul_one,mul_inv_cancel]
  | interchange hxy a b c f =>
    exact ⟨Equiv.sumSumSumComm _ _ _ _,sameBricks_interchange hxy a b c f,
      leafValue_interchange d q B g hxy a b c f⟩

/-- All equality between actual tree partitions follows from the finite colour
interchange law, including the induced full permutation of their leaves. -/
lemma leafValue_of_sameBricks (g:GridLaw d q B) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (he:SameBricks e) : leafValue d q B e=1 := by
  obtain ⟨f,hf,hv⟩ := (coherent_of_brickSet_eq a b he.brickSet_eq).exists_value_one d q B g
  rwa [← he.unique hf] at hv

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)

def structuralToEndpoint : StructuralQuotient x s →* EndpointQuotient x s t y₀ :=
  (decoratedToEndpoint x s t y₀).comp (structuralToDecorated x s t)
lemma structuralToEndpoint_project (g:Seed (Γ:=Γ) x) :
    structuralToEndpoint x s t y₀ (structuralProject x s g)=endpointProject x s t y₀ g := rfl
lemma structuralToEndpoint_surjective : Function.Surjective (structuralToEndpoint (Γ:=Γ) x s t y₀) :=
  (decoratedToEndpoint_surjective x s t y₀).comp (structuralToDecorated_surjective x s t)
lemma structuralToEndpoint_tensor (a b:StructuralQuotient (Γ:=Γ) x s) :
    structuralToEndpoint x s t y₀ (structuralTensor x s hs (a,b))=
      endpointTensor x s t y₀ hs (structuralToEndpoint x s t y₀ a,structuralToEndpoint x s t y₀ b) := by
  change decoratedToEndpoint x s t y₀ (structuralToDecorated x s t (structuralTensor x s hs (a,b)))=_
  rw [structuralToDecorated_tensor,decoratedToEndpoint_tensor]; rfl

/-- The finite endpoint quotient supplies the full binary symmetric structure. -/
def endpointData : Data (EndpointQuotient (Γ:=Γ) x s t y₀) where
  tensor := endpointTensor x s t y₀ hs
  a := endpointProject x s t y₀ (associatorWord x)
  naturality := by
    intro a b c
    obtain ⟨a,rfl⟩ := structuralToEndpoint_surjective x s t y₀ a
    obtain ⟨b,rfl⟩ := structuralToEndpoint_surjective x s t y₀ b
    obtain ⟨c,rfl⟩ := structuralToEndpoint_surjective x s t y₀ c
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralBinaryData x s hs).naturality a b c)
    simpa only [map_mul,map_inv,structuralBinaryData,structuralAssociator,
      structuralToEndpoint_project,structuralToEndpoint_tensor] using h
  pentagon := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralBinaryData x s hs).pentagon)
    simpa only [map_mul,map_one,structuralBinaryData,structuralAssociator,
      structuralToEndpoint_project,structuralToEndpoint_tensor] using h

def endpointSymmetryData : SymmetryData (endpointData (Γ:=Γ) x s t y₀ hs) where
  c := endpointProject x s t y₀ (flipWord x)
  square := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).square)
    simpa only [map_mul,map_one,structuralSymmetryData,structuralSymmetry,
      structuralToEndpoint_project] using h
  naturality := by
    intro a b
    obtain ⟨a,rfl⟩ := structuralToEndpoint_surjective x s t y₀ a
    obtain ⟨b,rfl⟩ := structuralToEndpoint_surjective x s t y₀ b
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).naturality a b)
    simpa only [map_mul,map_inv,structuralSymmetryData,structuralBinaryData,structuralSymmetry,
      structuralToEndpoint_project,structuralToEndpoint_tensor,endpointData] using h
  hexagon := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).hexagon)
    simpa only [map_mul,map_inv,map_one,structuralSymmetryData,structuralBinaryData,structuralSymmetry,
      structuralAssociator,structuralToEndpoint_project,structuralToEndpoint_tensor,endpointData] using h

lemma endpointProject_middleSwapWord : endpointProject x s t y₀ (middleSwapWord (Γ:=Γ) x)=
    middleSwap (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs) := by
  have h := congrArg (structuralToEndpoint x s t y₀) (structuralProject_middleSwapWord x s hs)
  simpa only [middleSwap,map_mul,map_inv,map_one,structuralToEndpoint_tensor,
    structuralToEndpoint_project,structuralBinaryData,structuralSymmetryData,
    structuralAssociator,structuralSymmetry,endpointData,endpointSymmetryData] using h

lemma endpointProject_gridWord (a b:X) : endpointProject x s t y₀ (gridWord (Γ:=Γ) x a b)=
    endpointBaker x s t y₀ hs a * endpointTensor x s t y₀ hs
      (endpointBaker x s t y₀ hs b,endpointBaker x s t y₀ hs b) := by
  have h := congrArg (decoratedToEndpoint x s t y₀) (decoratedProject_gridWord x s t hs a b)
  simpa only [decoratedToEndpoint_project,decoratedGrid,map_mul,decoratedToEndpoint_tensor,
    endpointBaker] using h

variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
include ht
lemma endpointBaker_base : endpointBaker x s t y₀ hs x=1 := by
  rw [endpointBaker,decoratedBaker_base x s t hs ht,map_one]
lemma endpointBaker_covariance (g:Γ) (y:X) :
    endpointRoot x s t y₀ g*endpointBaker x s t y₀ hs y=
      endpointBaker x s t y₀ hs (g • y)*endpointTensor x s t y₀ hs
        (endpointRoot x s t y₀ g,endpointRoot x s t y₀ g) := by
  have h := congrArg (decoratedToEndpoint x s t y₀) (decoratedBaker_covariance x s t hs ht g y)
  simpa only [map_mul,decoratedDiagonal_tensor,decoratedToEndpoint_tensor,
    decoratedToEndpoint_root,endpointBaker] using h

variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

include hxy htwo in
theorem endpointGridLaw : Tree.GridLaw (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
    (endpointBaker x s t y₀ hs) where
  grid a b hab := by
    have h := endpoint_interchange_all x s t hs ht y₀ hxy htwo a b hab
    simpa only [endpointProject_gridWord x s t y₀ hs,endpointData,
      endpointProject_middleSwapWord x s t y₀ hs] using h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

section
universe v w
open BinaryGroupCategory
variable {X:Type v} {H:Type w} [Group H] (d:Data H) (q:SymmetryData d) (B:X → H)

/-- Tensor leaf decorations along the literal coloured tree. -/
def fold : (a:Tree X) → (a.Leaves → H) → H
  | .leaf,F => F PUnit.unit
  | .split x a b,F => B x*d.tensor (fold a (fun i=>F (Sum.inl i)),
      fold b (fun i=>F (Sum.inr i)))*(B x)⁻¹

lemma fold_congr (a:Tree X) {F G:a.Leaves → H} (h:∀ i,F i=G i) : fold d B a F=fold d B a G :=
  congrArg (fold d B a) (funext h)

@[simp] lemma fold_one (a:Tree X) : fold d B a (fun _=>1)=1 := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    simp only [fold,ha,hb,show d.tensor (1,1)=1 from d.tensor.map_one,mul_one,mul_inv_cancel]

lemma fold_mul (a:Tree X) (F G:a.Leaves → H) :
    fold d B a (fun i=>F i*G i)=fold d B a F*fold d B a G := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    simp only [fold,ha,hb]
    rw [show d.tensor (fold d B a (fun i=>F (Sum.inl i))*fold d B a (fun i=>G (Sum.inl i)),
        fold d B b (fun i=>F (Sum.inr i))*fold d B b (fun i=>G (Sum.inr i)))=
      d.tensor (fold d B a (fun i=>F (Sum.inl i)),fold d B b (fun i=>F (Sum.inr i)))*
      d.tensor (fold d B a (fun i=>G (Sum.inl i)),fold d B b (fun i=>G (Sum.inr i))) from
      d.tensor.map_mul (fold d B a (fun i=>F (Sum.inl i)),fold d B b (fun i=>F (Sum.inr i)))
        (fold d B a (fun i=>G (Sum.inl i)),fold d B b (fun i=>G (Sum.inr i)))]
    group

lemma fold_inv (a:Tree X) (F:a.Leaves → H) : fold d B a (fun i=>(F i)⁻¹)=(fold d B a F)⁻¹ := by
  have h := fold_mul d B a F (fun i=>(F i)⁻¹)
  simp only [mul_inv_cancel,fold_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Substitution of arbitrary decorated trees at all leaves. -/
lemma fold_graft (a:Tree X) (F:a.Leaves → Tree X) (L:(a.graft F).Leaves → H) :
    fold d B (a.graft F) L=fold d B a
      (fun i=>fold d B (F i) (fun j=>L ((a.graftLeaves F).symm ⟨i,j⟩))) := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    change B x*d.tensor (fold d B (a.graft _) (fun i=>L (Sum.inl i)),
      fold d B (b.graft _) (fun i=>L (Sum.inr i)))*(B x)⁻¹=_
    rw [ha,hb]
    rfl

/-- Scalar naturality for a tensor square, preventing dependent tree rewrites. -/
lemma tensor_square (A C U V F G I J:H)
    (h₁:U*F=I*U) (h₂:V*G=J*V) :
    (C*d.tensor (U,V)*A⁻¹)*(A*d.tensor (F,G)*A⁻¹)=
      (C*d.tensor (I,J)*C⁻¹)*(C*d.tensor (U,V)*A⁻¹) := by
  have hh : d.tensor (U,V)*d.tensor (F,G)=d.tensor (I,J)*d.tensor (U,V) := by
    rw [← map_mul,← map_mul]; exact congrArg d.tensor (Prod.ext h₁ h₂)
  calc
    _=C*(d.tensor (U,V)*d.tensor (F,G))*A⁻¹ := by group
    _=_ := by rw [hh]; group

/-- Flatten nested conjugations in a left-associated tree. -/
lemma fold_left_algebra (x y:X) (A C E:H) :
    B x*d.tensor (B y*d.tensor (A,C)*(B y)⁻¹,E)*(B x)⁻¹=
      (B x*d.tensor (B y,1))*d.tensor (d.tensor (A,C),E)*(B x*d.tensor (B y,1))⁻¹ := by
  have h := tensor_conjugate d (B y) 1 (d.tensor (A,C)) E
  simp only [inv_one,one_mul,mul_one] at h
  rw [h]
  group
lemma fold_right_algebra (x y:X) (A C E:H) :
    B x*d.tensor (A,B y*d.tensor (C,E)*(B y)⁻¹)*(B x)⁻¹=
      (B x*d.tensor (1,B y))*d.tensor (A,d.tensor (C,E))*(B x*d.tensor (1,B y))⁻¹ := by
  have h := tensor_conjugate d 1 (B y) A (d.tensor (C,E))
  simp only [inv_one,one_mul,mul_one] at h
  rw [h]
  group

lemma leafValue_fold_route {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (r:Route e)
    (F:a.Leaves → H) (G:b.Leaves → H) (h:∀ i,F i=G (e i)) :
    leafValue d q B e*fold d B a F=fold d B b G*leafValue d q B e := by
  induction r with
  | refl a => rw [leafValue_refl,one_mul,mul_one]; exact fold_congr d B a h
  | @trans a b c e f r s ih ik =>
    let M := fun j=>F (e.symm j)
    have h₁ := ih F M (by intro i; simp [M])
    have h₂ := ik M G (by intro j; simpa [M] using h (e.symm j))
    rw [leafValue_trans]
    calc
      _=leafValue d q B f*(leafValue d q B e*fold d B a F) := by group
      _=_ := by rw [h₁,← mul_assoc,h₂]; group
  | @symm a b e r ih =>
    have hh := ih G F (by intro i; simpa using (h (e i)).symm)
    rw [leafValue_symm]
    calc
      _=(leafValue d q B e)⁻¹*(fold d B b F*leafValue d q B e)*(leafValue d q B e)⁻¹ := by group
      _=_ := by rw [← hh]; group
  | @sum a b c f x y e g r s ih ik =>
    rw [leafValue_sum]
    exact tensor_square d (B x) (B y) _ _ _ _ _ _
      (ih (fun i=>F (Sum.inl i)) (fun i=>G (Sum.inl i)) (fun i=>h (Sum.inl i)))
      (ik (fun i=>F (Sum.inr i)) (fun i=>G (Sum.inr i)) (fun i=>h (Sum.inr i)))
  | assoc x y z w a b c =>
    have h₁ := fold_congr d B a (fun i=>h (Sum.inl (Sum.inl i)))
    have h₂ := fold_congr d B b (fun i=>h (Sum.inl (Sum.inr i)))
    have h₃ := fold_congr d B c (fun i=>h (Sum.inr i))
    rw [leafValue_assoc]
    simp only [fold]
    rw [h₁,h₂,h₃,fold_left_algebra,fold_right_algebra]
    simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,Equiv.sumAssoc_apply_inr]
    have hn := d.naturality (fold d B a (fun i=>G (Sum.inl i)))
      (fold d B b (fun i=>G (Sum.inr (Sum.inl i))))
      (fold d B c (fun i=>G (Sum.inr (Sum.inr i))))
    rw [← hn]
    group
  | exchange x y a b =>
    have h₁ := fold_congr d B a (fun i=>h (Sum.inl i))
    have h₂ := fold_congr d B b (fun i=>h (Sum.inr i))
    rw [leafValue_exchange]
    simp only [fold]
    rw [h₁,h₂]
    simp only [Equiv.sumComm_apply,Sum.swap_inl,Sum.swap_inr]
    have hn := q.naturality (fold d B a (fun i=>G (Sum.inr i)))
      (fold d B b (fun i=>G (Sum.inl i)))
    rw [← hn]
    group

lemma leafValue_fold (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (F:a.Leaves → H) (G:b.Leaves → H) (h:∀ i,F i=G (e i)) :
    leafValue d q B e*fold d B a F=fold d B b G*leafValue d q B e :=
  leafValue_fold_route d q B (route_complete x e) F G h

/-- Whole dependent substitution of a bijection and bijections in every fibre. -/
def graftMap {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) : (a.graft F).Leaves ≃ (b.graft G).Leaves :=
  (a.graftLeaves F).trans ((Equiv.sigmaCongr e h).trans (b.graftLeaves G).symm)
lemma graftMap_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) (i:a.Leaves) (j:(F i).Leaves) :
    graftMap e F G h ((a.graftLeaves F).symm ⟨i,j⟩)=(b.graftLeaves G).symm ⟨e i,h i j⟩ := by
  simp [graftMap,Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft]

lemma graftMap_leaf (F G:(Tree.leaf:Tree X).Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) : graftMap (Equiv.refl _) F G h=h PUnit.unit := by
  apply Equiv.ext; intro j
  exact graftMap_apply (Equiv.refl _) F G h PUnit.unit j

lemma graftMap_sum (x:X) (a b:Tree X) (F G:(Tree.split x a b).Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) :
    graftMap (Equiv.refl _) F G h=
      Equiv.sumCongr (graftMap (Equiv.refl a.Leaves) (fun i=>F (Sum.inl i))
        (fun i=>G (Sum.inl i)) (fun i=>h (Sum.inl i)))
      (graftMap (Equiv.refl b.Leaves) (fun i=>F (Sum.inr i))
        (fun i=>G (Sum.inr i)) (fun i=>h (Sum.inr i))) := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftMap (a:=.split x a b) (Equiv.refl _) F G h
      (((Tree.split x a b).graftLeaves F).symm ⟨Sum.inl i,k⟩)=_
    erw [graftMap_apply]
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr i))).symm.surjective j
    change graftMap (a:=.split x a b) (Equiv.refl _) F G h
      (((Tree.split x a b).graftLeaves F).symm ⟨Sum.inr i,k⟩)=_
    erw [graftMap_apply]

lemma leafValue_graftWithin (a:Tree X) (F G:a.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) :
    leafValue d q B (graftMap (Equiv.refl _) F G h)=fold d B a (fun i=>leafValue d q B (h i)) := by
  induction a with
  | leaf => rw [graftMap_leaf]; rfl
  | split x a b ha hb =>
    rw [graftMap_sum]
    change leafValue d q B (a:=.split x (a.graft _) (b.graft _))
      (b:=.split x (a.graft _) (b.graft _)) (Equiv.sumCongr _ _)=_
    rw [leafValue_sum,ha,hb]; rfl

lemma graftMap_factor {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) : graftMap e F G h=
      (graftMap (Equiv.refl _) F (fun i=>G (e i)) h).trans (graftLift e G) := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves F).symm.surjective j
  calc
    _=(b.graftLeaves G).symm ⟨e i,h i k⟩ := graftMap_apply e F G h i k
    _=graftLift e G ((a.graftLeaves (fun i=>G (e i))).symm ⟨i,h i k⟩) :=
      (graftLift_apply e G i (h i k)).symm
    _=_ := congrArg (graftLift e G) (graftMap_apply (Equiv.refl _) F (fun i=>G (e i)) h i k).symm

lemma leafValue_graftMap (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (F:a.Leaves → Tree X) (G:b.Leaves → Tree X) (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) :
    leafValue d q B (graftMap e F G h)=leafValue d q B e*fold d B a (fun i=>leafValue d q B (h i)) := by
  rw [graftMap_factor,leafValue_trans,leafValue_graftLift d q B x,leafValue_graftWithin]

end

universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
variable (d:Data H) (q:SymmetryData d) (B:X → H)

/-- Leaf transport of a coordinate relabelling, with the same binary shape. -/
def colourLeaves (f:X → X) : (a:Tree X) → a.Leaves ≃ (mapColors f a).Leaves
  | .leaf => Equiv.refl _
  | .split _ a b => Equiv.sumCongr (colourLeaves f a) (colourLeaves f b)

lemma colour_brick (g:Γ) (a:Tree X) (i:a.Leaves) :
    (mapColors (fun x=>g • x) a).brick (colourLeaves (fun x=>g • x) a i)=twistPrefix g (a.brick i) := by
  induction a with
  | leaf => exact (twistPrefix_empty g).symm
  | split x a b ha hb =>
    cases i with
    | inl i =>
      change (Prefix.oneBit (g • x) false).comp ((mapColors (fun x=>g • x) a).brick _)=_
      rw [ha,brick,twistPrefix_comp,twistPrefix_oneBit]
    | inr i =>
      change (Prefix.oneBit (g • x) true).comp ((mapColors (fun x=>g • x) b).brick _)=_
      rw [hb,brick,twistPrefix_comp,twistPrefix_oneBit]

/-- Root-label splitting, derived solely from the proved baker covariance law. -/
lemma leafValue_colour (R:Γ →* H)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (g:Γ) (a:Tree X) :
    leafValue d q B (colourLeaves (fun x=>g • x) a)*fold d B a (fun _=>R g)=R g := by
  induction a with
  | leaf =>
    change leafValue d q B (a:=.leaf) (b:=.leaf) (Equiv.refl _)*R g=R g
    rw [leafValue_refl,one_mul]
  | split x a b ha hb =>
    change leafValue d q B (a:=.split x a b)
      (b:=.split (g • x) (mapColors (fun x=>g • x) a) (mapColors (fun x=>g • x) b))
      (Equiv.sumCongr _ _)*(B x*d.tensor (fold d B a (fun _=>R g),fold d B b (fun _=>R g))*(B x)⁻¹)=_
    rw [leafValue_sum]
    calc
      _=B (g • x)*(d.tensor (leafValue d q B (colourLeaves (fun x=>g • x) a),
          leafValue d q B (colourLeaves (fun x=>g • x) b))*
        d.tensor (fold d B a (fun _=>R g),fold d B b (fun _=>R g)))*(B x)⁻¹ := by group
      _=B (g • x)*d.tensor (R g,R g)*(B x)⁻¹ := by
        rw [← map_mul]; change B (g • x)*d.tensor (_*_,_*_)*(B x)⁻¹=_; rw [ha,hb]
      _=R g := by rw [← hR]; group

lemma leafValue_uncolour (x:X) (R:Γ →* H)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (g:Γ) (a:Tree X) :
    leafValue d q B (colourLeaves (fun x=>g⁻¹ • x) a).symm*
      fold d B (mapColors (fun x=>g⁻¹ • x) a) (fun _=>R g)=R g := by
  have hh := congrArg (fun z:H=>z⁻¹) (leafValue_colour d q B R hR g⁻¹ a)
  simp only [mul_inv_rev,map_inv] at hh
  rw [← fold_inv] at hh
  simp only [inv_inv] at hh
  calc
    _=fold d B a (fun _=>R g)*leafValue d q B (colourLeaves (fun x=>g⁻¹ • x) a).symm :=
      leafValue_fold d q B x _ _ _ (fun _=>rfl)
    _=R g := by rw [leafValue_symm]; exact hh

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

end

end OAI
