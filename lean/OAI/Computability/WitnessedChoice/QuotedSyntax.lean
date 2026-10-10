import OAI.Computability.WitnessedChoice.Syntax

namespace OAI


namespace WitnessedChoice.RelationPools

noncomputable section

open Classical

variable {A : Type} [Fintype A]

abbrev Relation (A : Type) := Finset (A × A)

def graph (g : Equiv.Perm A) : Relation A := Finset.univ.image (fun a => (a,g a))

@[simp] lemma mem_graph (g : Equiv.Perm A) (a b : A) :
    (a,b) ∈ graph g ↔ g a = b := by
  simp [graph]

lemma graph_injective : Function.Injective (graph : Equiv.Perm A → Relation A) := by
  intro g h he
  apply Equiv.ext
  intro a
  have hh : (a,g a) ∈ graph h := by rw [← he]; simp
  exact (mem_graph h a (g a)).mp hh |>.symm

def compose (l c : Relation A) : Relation A := Finset.univ.filter fun ab =>
  ∃ u, (ab.1,u) ∈ l ∧ (u,ab.2) ∈ c

@[simp] lemma mem_compose (l c : Relation A) (a b : A) :
    (a,b) ∈ compose l c ↔ ∃ u, (a,u) ∈ l ∧ (u,b) ∈ c := by
  simp [compose]

@[simp] lemma compose_graph (g h : Equiv.Perm A) :
    compose (graph g) (graph h) = graph (h*g) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp [Equiv.Perm.mul_apply]

@[irreducible] def localBound : ℕ := 16*(3^9+3^29)

def localRelation {B : ℕ} (p q : Fin B → A) : Relation A :=
  (Finset.univ.image (fun i => (p i,q i))) ∪
    ((Finset.univ.filter (fun a => ∀ i, a ≠ p i)).image (fun a => (a,a)))

def localPool (B : ℕ) : Finset (Relation A) :=
  insert (graph 1) (Finset.univ.image (fun pq : (Fin B → A) × (Fin B → A) =>
    localRelation pq.1 pq.2))

lemma identity_mem_localPool (B : ℕ) : graph (1 : Equiv.Perm A) ∈ localPool B := by
  exact Finset.mem_insert_self _ _

lemma localPool_contains {B : ℕ} (g : Equiv.Perm A)
    (hb : (Finset.univ.filter (fun a => g a ≠ a)).card ≤ B) : graph g ∈ localPool B := by
  let s : Finset A := Finset.univ.filter (fun a => g a ≠ a)
  by_cases hs : s.Nonempty
  · obtain ⟨a0, ha0⟩ := hs
    let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (by simp)
    let p : Fin B → A := fun i => if hi : i.val < s.card then (e.symm ⟨i.val,hi⟩).val else a0
    let q : Fin B → A := g ∘ p
    have cover : ∀ a ∈ s, ∃ i, p i = a := by
      intro a ha
      let j := e ⟨a,ha⟩
      let i : Fin B := ⟨j.val, lt_of_lt_of_le j.isLt hb⟩
      refine ⟨i,?_⟩
      dsimp [p]
      rw [dite_eq_left j.isLt]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨a,ha⟩)
    have he : localRelation p q = graph g := by
      ext ab
      rcases ab with ⟨a,b⟩
      simp only [localRelation, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and, Finset.mem_filter, Prod.mk.injEq, mem_graph]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨u, hu, rfl, rfl⟩)
        · rw [← hi]; rfl
        · by_contra hn
          obtain ⟨i,hi⟩ := cover u (by simpa [s] using hn)
          exact hu i hi.symm
      · intro hg
        by_cases ha : a ∈ s
        · obtain ⟨i,hi⟩ := cover a ha
          exact Or.inl ⟨i,hi,by dsimp [q,Function.comp_apply]; rw [hi,hg]⟩
        · right
          have hga : g a = a := by simpa [s] using ha
          refine ⟨a,?_,rfl,hga.symm.trans hg⟩
          intro i hai
          have hp : p i ∈ s := by
            dsimp [p]
            split
            · exact (e.symm _).property
            · exact ha0
          exact ha (hai ▸ hp)
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(p,q),Finset.mem_univ _,he⟩
  · have hg : g = 1 := by
      apply Equiv.ext
      intro a
      by_contra hn
      exact hs ⟨a,by simpa [s] using hn⟩
    rw [hg]
    exact identity_mem_localPool B

lemma localPool_card_le (B : ℕ) :
    (localPool (A := A) B).card ≤ 1 + Fintype.card A ^ (2*B) := by
  calc
    (localPool (A := A) B).card ≤
      (Finset.univ.image (fun pq : (Fin B → A) × (Fin B → A) => localRelation pq.1 pq.2)).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ Fintype.card ((Fin B → A) × (Fin B → A)) + 1 :=
      Nat.add_le_add_right (Finset.card_image_le) 1
    _ = 1 + Fintype.card A ^ (2*B) := by
      simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
      rw [← pow_add,two_mul]
      omega

def rename (g : Equiv.Perm A) (r : Relation A) : Relation A :=
  r.image (fun ab => (g ab.1,g ab.2))

@[simp] lemma rename_graph (h g : Equiv.Perm A) :
    rename h (graph g) = graph (h*g*h⁻¹) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp only [rename,Finset.mem_image,Prod.exists,Prod.mk.injEq,mem_graph]
  constructor
  · rintro ⟨u,v,hv,rfl,rfl⟩
    simpa [Equiv.Perm.mul_apply] using congrArg h hv
  · intro he
    refine ⟨h⁻¹ a,h⁻¹ b,?_,by simp,by simp⟩
    apply h.injective
    simpa [Equiv.Perm.mul_apply] using he

lemma rename_compose (h : Equiv.Perm A) (l c : Relation A) :
    rename h (compose l c) = compose (rename h l) (rename h c) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp only [rename,Finset.mem_image,Prod.exists,Prod.mk.injEq,mem_compose]
  constructor
  · rintro ⟨u,v,⟨w,hl,hc⟩,rfl,rfl⟩
    exact ⟨h w,⟨u,w,hl,rfl,rfl⟩,⟨w,v,hc,rfl,rfl⟩⟩
  · rintro ⟨w,⟨u,z,hl,rfl,hu⟩,⟨z',v,hc,hv,rfl⟩⟩
    have hz : z = z' := h.injective (hu.trans hv.symm)
    subst z'
    exact ⟨u,v,⟨z,hl,hc⟩,rfl,rfl⟩

lemma rename_localRelation {B : ℕ} (h : Equiv.Perm A) (p q : Fin B → A) :
    rename h (localRelation p q) = localRelation (h ∘ p) (h ∘ q) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp only [rename,localRelation,Finset.mem_image,Finset.mem_union,Finset.mem_filter,
    Finset.mem_univ,true_and,Prod.exists,Prod.mk.injEq,Function.comp_apply]
  constructor
  · rintro ⟨u,v,(⟨i,hu,hv⟩|⟨w,hw,hu,hv⟩),rfl,rfl⟩
    · exact Or.inl ⟨i,congrArg h hu,congrArg h hv⟩
    · subst u; subst v
      exact Or.inr ⟨h w,fun i hi => hw i (h.injective hi),rfl,rfl⟩
  · rintro (⟨i,rfl,rfl⟩|⟨w,hw,rfl,rfl⟩)
    · exact ⟨p i,q i,Or.inl ⟨i,rfl,rfl⟩,rfl,rfl⟩
    · refine ⟨h⁻¹ w,h⁻¹ w,Or.inr ⟨h⁻¹ w,?_,rfl,rfl⟩,by simp,by simp⟩
      intro i hi
      exact hw i (by simpa using congrArg h hi)

lemma localPool_equivariant (B : ℕ) (h : Equiv.Perm A) :
    (localPool B).image (rename h) = localPool (A := A) B := by
  unfold localPool
  rw [Finset.image_insert,rename_graph]
  simp only [mul_one,mul_inv_cancel]
  congr 1
  ext r
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨l,⟨p,q,rfl⟩,rfl⟩
    exact ⟨h ∘ p,h ∘ q,(rename_localRelation h p q).symm⟩
  · rintro ⟨p,q,rfl⟩
    refine ⟨localRelation ((h⁻¹ : Equiv.Perm A) ∘ p) ((h⁻¹ : Equiv.Perm A) ∘ q),⟨_,_,rfl⟩,?_⟩
    rw [rename_localRelation]
    congr 1 <;> funext i <;> simp

end

end WitnessedChoice.RelationPools



namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

variable {A : Type} [Fintype A]

def edgeAtoms (S : Input A) : Finset A := Finset.univ.filter fun a => S.rel .Ed a a = true

def configAtoms (S : Input A) : Finset A := Finset.univ.filter fun a => S.rel .Cf a a = true

def edgeRow (S : Input A) (a : A) : Finset A := (edgeAtoms S).filter fun s => S.rel .EB a s = true

def vertexRow (S : Input A) (a : A) : Finset A := (configAtoms S).filter fun s => S.rel .VB a s = true

def edgeBlocks (S : Input A) : Finset (Finset A) := (edgeAtoms S).image (edgeRow S)

def vertexBlocks (S : Input A) : Finset (Finset A) := (configAtoms S).image (vertexRow S)

def blocks (S : Input A) : Finset (Finset A) := edgeBlocks S ∪ vertexBlocks S

def tupleCode : List (HF A) → HF A
  | [] => ordinal 0
  | x::xs => pair x (tupleCode xs)

def parameterCode (α : Fin 4 → Finset A) : HF A := tupleCode (List.ofFn (stateCode ∘ α))

omit [Fintype A] in
lemma smul_pair (g : Equiv.Perm A) (x y : HF A) :
    g • pair x y = pair (g • x) (g • y) := map_pair g x y

omit [Fintype A] in
lemma tupleCode_fixed (g : Equiv.Perm A) (xs : List (HF A))
    (h : ∀ x ∈ xs, g • x = x) : g • tupleCode xs = tupleCode xs := by
  induction xs with
  | nil => simp [tupleCode,ordinal,smul_ofFinset]
  | cons x xs ih =>
    simp only [tupleCode,smul_pair]
    rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

omit [Fintype A] in
lemma parameterCode_fixed (g : Equiv.Perm A) (α : Fin 4 → Finset A)
    (h : ∀ i, (α i).image g = α i) : g • parameterCode α = parameterCode α := by
  apply tupleCode_fixed
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  dsimp [Function.comp_apply]
  rw [smul_stateCode,h i]

variable (B : ℕ)

def PoolFilter (S : Input A) (x : Finset A) (g : Equiv.Perm A) : Prop :=
  g ∈ fullAut S ∧ (∀ u ∈ blocks S, u.image g = u) ∧ ∀ a ∈ x, g a = a

def witnessPool (S : Input A) (valid : Prop) (cyclePool : Finset A → Finset (Relation A))
    (x : Finset A) : Finset (Equiv.Perm A) :=
  if valid then insert 1 (Finset.univ.filter fun g => PoolFilter S x g ∧
    ∃ l ∈ localPool B, ∃ c ∈ cyclePool x, compose l c = graph g)
  else {1}

def guardedSelection (S : Input A) (valid : Prop) (D : Finset A → Finset A)
    (C : Finset A → Finset (Relation A)) : Selection A where
  candidates := fun x => if valid then D x else ∅
  witnesses := witnessPool B S valid C

lemma one_mem_witnessPool (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) :
    (1 : Equiv.Perm A) ∈ witnessPool B S valid C x := by
  unfold witnessPool
  split_ifs <;> simp

lemma witnessPool_filter (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) {g : Equiv.Perm A}
    (h : g ∈ witnessPool B S valid C x) : PoolFilter S x g := by
  unfold witnessPool at h
  split_ifs at h
  · rcases Finset.mem_insert.mp h with rfl | h
    · exact ⟨(fullAut S).one_mem,by simp,by simp⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.1
  · have hg : g = 1 := Finset.mem_singleton.mp h
    subst g
    exact ⟨(fullAut S).one_mem,by simp,by simp⟩

theorem guardedSelection_filtered (S : Input A) (valid : Prop)
    (D : Finset A → Finset A) (C : Finset A → Finset (Relation A))
    (α : Fin 4 → Finset A) (hα : ∀ i, α i ∈ blocks S) :
    (guardedSelection B S valid D C).Filtered S (parameterCode α) := by
  refine ⟨one_mem_witnessPool B S valid C,?_,?_⟩
  · intro x g hg
    obtain ⟨ha,hb,_⟩ := witnessPool_filter B S valid C x hg
    exact ⟨ha,parameterCode_fixed g α (fun i => hb (α i) (hα i))⟩
  · intro x g hg
    exact (witnessPool_filter B S valid C x hg).2.2

theorem guardedSelection_invalid_filtered (S : Input A) (valid : Prop) (hv : ¬ valid)
    (D : Finset A → Finset A) (C : Finset A → Finset (Relation A)) (α : HF A) :
    (guardedSelection B S valid D C).Filtered S α := by
  refine ⟨one_mem_witnessPool B S valid C,?_,?_⟩
  · intro x g hg
    have hg' : g = 1 := by simpa [guardedSelection,witnessPool,hv] using hg
    subst g
    exact (paramAut S α).one_mem
  · intro x g hg a ha
    have hg' : g = 1 := by simpa [guardedSelection,witnessPool,hv] using hg
    subst g
    rfl

lemma composition_mem_witnessPool (S : Input A) (valid : Prop) (hv : valid)
    (C : Finset A → Finset (Relation A)) (x : Finset A) (l c : Equiv.Perm A)
    (hl : (Finset.univ.filter (fun a => l a ≠ a)).card ≤ B)
    (hc : graph c ∈ C x) (hg : PoolFilter S x (c*l)) :
    c*l ∈ witnessPool B S valid C x := by
  rw [witnessPool,ite_eq_left hv]
  apply Finset.mem_insert_of_mem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hg,graph l,localPool_contains l hl,graph c,hc,?_⟩
  exact compose_graph l c

lemma witnessPool_card_le (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) :
    (witnessPool B S valid C x).card ≤ 1 +
      (1 + Fintype.card A ^ (2*B)) * (C x).card := by
  by_cases hv : valid
  · let W := Finset.univ.filter (fun g : Equiv.Perm A => PoolFilter S x g ∧
      ∃ l ∈ localPool B, ∃ c ∈ C x, compose l c = graph g)
    let R := ((localPool (A := A) B).product (C x)).image fun lc => compose lc.1 lc.2
    have hsub : W.image graph ⊆ R := by
      intro r hr
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
      dsimp only [W] at hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      obtain ⟨_,l,hl,c,hc,he⟩ := hg
      exact Finset.mem_image.mpr ⟨(l,c),Finset.mem_product.mpr ⟨hl,hc⟩,he⟩
    have hcard : W.card ≤ (localPool (A := A) B).card * (C x).card := by
      calc
        W.card = (W.image graph).card := (Finset.card_image_of_injective _ graph_injective).symm
        _ ≤ R.card := Finset.card_le_card hsub
        _ ≤ ((localPool (A := A) B).product (C x)).card := Finset.card_image_le
        _ = _ := Finset.card_product _ _
    change (witnessPool B S valid C x).card ≤ _
    rw [witnessPool,ite_eq_left hv]
    change (insert 1 W).card ≤ _
    have he := localPool_card_le (A := A) B
    have hm := Nat.mul_le_mul_right (C x).card he
    exact (Finset.card_insert_le _ _).trans (by omega)
  · simp [witnessPool,hv]

end

end WitnessedChoice



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type}

def pairCode (ab : A × A) : HF A := pair (atom ab.1) (atom ab.2)

def relationCode (r : Relation A) : HF A := ofFinset (r.image pairCode)

lemma pairCode_injective : Function.Injective (pairCode (A := A)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hh := pair_injective h
  exact Prod.ext (atom_injective hh.1) (atom_injective hh.2)

@[simp] lemma pairCode_eq {ab cd : A × A} : pairCode ab = pairCode cd ↔ ab = cd :=
  pairCode_injective.eq_iff

lemma relationCode_injective : Function.Injective (relationCode (A := A)) := by
  intro r s he
  exact (Finset.image_injective pairCode_injective) (ofFinset_inj.mp he)

@[simp] lemma elements_relationCode (r : Relation A) : elements (relationCode r) = r.image pairCode :=
  elements_ofFinset _

@[simp] lemma relationCode_empty : relationCode (∅ : Relation A) = emptyHF := by
  simp [relationCode,emptyHF]

@[simp] lemma relationCode_insert (ab : A × A) (r : Relation A) :
    relationCode (insert ab r) = ofFinset (insert (pairCode ab) (elements (relationCode r))) := by
  simp only [relationCode,Finset.image_insert,elements_ofFinset]

variable [Fintype A]

@[simp] lemma relationCode_graph (g : Equiv.Perm A) : relationCode (graph g) = permutationGraph g := by
  simp only [relationCode,graph,permutationGraph,Finset.image_image,pairCode,Function.comp_def]

def partialRelations : ℕ → Finset (Relation A)
  | 0 => {∅}
  | k+1 => (partialRelations k).biUnion fun r => Finset.univ.biUnion fun a : A =>
      Finset.univ.image fun b : A => insert (a,b) r

omit [Fintype A] in
lemma tupleImage_cons {B : ℕ} (p q : Fin B → A) (a b : A) :
    (Finset.univ.image (fun i => (Fin.cons a p i,Fin.cons b q i))) =
      insert (a,b) (Finset.univ.image (fun i => (p i,q i))) := by
  ext cd
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩
  · rintro (rfl|⟨j,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨j.succ,rfl⟩

lemma partialRelations_eq (B : ℕ) : partialRelations (A := A) B =
    Finset.univ.image (fun pq : (Fin B → A) × (Fin B → A) =>
      Finset.univ.image (fun i => (pq.1 i,pq.2 i))) := by
  induction B with
  | zero =>
    ext r
    simp only [partialRelations,Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,
      true_and,Prod.exists]
    constructor
    · rintro rfl
      exact ⟨Fin.elim0,Fin.elim0,by simp⟩
    · rintro ⟨p,q,rfl⟩
      simp
  | succ B ih =>
    ext r
    simp only [partialRelations,ih,Finset.mem_biUnion,Finset.mem_image,
      Finset.mem_univ,true_and,Prod.exists]
    constructor
    · rintro ⟨r,⟨p,q,rfl⟩,a,b,rfl⟩
      exact ⟨Fin.cons a p,Fin.cons b q,tupleImage_cons p q a b⟩
    · rintro ⟨p,q,rfl⟩
      refine ⟨Finset.univ.image (fun i => (Fin.tail p i,Fin.tail q i)),
        ⟨Fin.tail p,Fin.tail q,rfl⟩,p 0,q 0,?_⟩
      simpa only [Fin.cons_self_tail] using (tupleImage_cons (Fin.tail p) (Fin.tail q) (p 0) (q 0)).symm

lemma Term.eval_partialPool (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (B : ℕ) (env : Fin n → HF A) :
    (Term.partialPool B).eval S p env =
      some (ofFinset ((partialRelations (A := A) B).image relationCode)) := by
  induction B with
  | zero =>
    simpa only [partialPool,partialRelations,Finset.image_singleton,relationCode_empty,
      Hereditary.singleton] using Term.eval_singleton S p (Term.empty) env rfl
  | succ B ih =>
    have hb (r : HF A) :
        (Term.atoms.bindSet (Term.atoms.mapSet (Term.addPairBody (n := n)))).eval S p
          (Fin.cons r env) = some (ofFinset (Finset.univ.biUnion fun a : A =>
            Finset.univ.image fun b : A => ofFinset (insert (pairCode (a,b)) (elements r)))) := by
      have hmap (a : HF A) := Term.eval_mapSet S p Term.atoms Term.addPairBody
        (Fin.cons a (Fin.cons r env)) rfl
        (fun b => Term.eval_addPairBody S p env r a b)
      have hh := Term.eval_bindSet S p Term.atoms (Term.atoms.mapSet Term.addPairBody)
        (Fin.cons r env) rfl hmap
      simpa only [elements_ofFinset,Finset.image_biUnion,Finset.image_image,
        Function.comp_def,pairCode] using hh
    have hh := Term.eval_bindSet S p (Term.partialPool B)
      (Term.atoms.bindSet (Term.atoms.mapSet Term.addPairBody)) env ih hb
    change _ = _ at hh
    convert hh using 1
    congr 2
    simp only [partialRelations,Finset.biUnion_image,Finset.image_image,
      elements_ofFinset,Finset.image_biUnion,Function.comp_def,relationCode_insert]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

def completeHF (r : HF A) : HF A := ofFinset (elements r ∪
  ((Finset.univ.filter fun a : A => ∀ b : A, pairCode (a,b) ∉ elements r).image
    (fun a => pairCode (a,a))))

lemma Term.eval_completeRelation (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) (r : HF A) :
    (Term.completeRelation (n := n)).eval S p (Fin.cons r env) = some (completeHF r) := by
  have hg (a : HF A) :
      (Formula.neg (Formula.existsIn Term.atoms (Formula.mem
        (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2)))).eval S p
        (Fin.cons a (Fin.cons r env)) =
      some (decide (∀ b : A, Hereditary.pair a (atom b) ∉ elements r)) := by
    have hm (b : HF A) := Formula.eval_mem S p
      (Term.orderedPair (Term.var (1 : Fin (n+3))) (Term.var 0)) (Term.var 2) rfl
      (Fin.cons b (Fin.cons a (Fin.cons r env)))
      (Term.eval_orderedPair S p _ _ _ rfl rfl) rfl
    have hh := Formula.eval_existsIn S p Term.atoms
      (Formula.mem (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2))
      (Fin.cons a (Fin.cons r env)) rfl hm
    simp only [Formula.eval,hh,Option.map_some]
    simp only [elements_ofFinset,Fin.cons_one,cons_two,Fin.cons_zero,
      Finset.mem_image,Finset.mem_univ,true_and,decide_eq_true_eq]
    by_cases h : ∃ b : A, Hereditary.pair a (atom b) ∈ elements r
    · obtain ⟨b,hb⟩ := h
      have he : ∃ b : A, Hereditary.pair a (atom b) ∈ elements r := ⟨b,hb⟩
      have hn : ¬ ∀ b : A, Hereditary.pair a (atom b) ∉ elements r := fun h => h b hb
      simp [he,hn]
    · simp only [not_exists] at h
      simp [h]
  have hb (a : HF A) := Term.eval_orderedPair S p (Term.var (0 : Fin (n+2))) (Term.var 0)
    (Fin.cons a (Fin.cons r env)) rfl rfl
  have hh := Term.eval_comprehend S p Term.atoms
    (Term.orderedPair (Term.var 0) (Term.var 0))
    (Formula.neg (Formula.existsIn Term.atoms (Formula.mem
      (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2))))
    (Fin.cons r env) rfl hb hg
  have hc := Term.eval_cup S p (Term.var (0 : Fin (n+1))) _ (Fin.cons r env) rfl hh
  have hc' : (Term.completeRelation (n := n)).eval S p (Fin.cons r env) =
      some (ofFinset (elements r ∪ (((Finset.univ.image atom).filter
        (fun a : HF A => decide (∀ b : A, Hereditary.pair a (atom b) ∉ elements r) = true)).image
        (fun a => Hereditary.pair a a)))) := by
    simpa only [completeRelation,elements_ofFinset,Fin.cons_zero] using hc
  rw [hc']
  apply congrArg some
  unfold completeHF
  apply congrArg ofFinset
  apply congrArg (fun z => elements r ∪ z)
  symm
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    decide_eq_true_eq,pairCode]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨atom a,⟨⟨a,rfl⟩,(Finset.mem_filter.mp ha).2⟩,rfl⟩
  · rintro ⟨z,⟨⟨a,rfl⟩,ha⟩,rfl⟩
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩

omit [Fintype A] in
@[simp] lemma mem_elements_relationCode (r : Relation A) (a b : A) :
    pairCode (a,b) ∈ elements (relationCode r) ↔ (a,b) ∈ r := by
  simp [relationCode,pairCode_injective.mem_finset_image]

lemma completeHF_tuple {B : ℕ} (p q : Fin B → A) :
    completeHF (relationCode (Finset.univ.image (fun i => (p i,q i)))) =
      relationCode (localRelation p q) := by
  apply ofFinset_inj.mpr
  simp only [relationCode,elements_ofFinset,localRelation,Finset.image_union]
  congr 1
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    pairCode_eq]
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(a,a),⟨a,?_,rfl⟩,rfl⟩
    intro i hi
    apply ha (q i)
    exact ⟨(p i,q i),⟨i,rfl⟩,by rw [hi]⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨a,?_,rfl⟩
    rintro b ⟨_,⟨i,rfl⟩,he⟩
    exact ha i (congrArg Prod.fst he).symm

lemma Term.eval_identityRelation (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) :
    (Term.identityRelation (n := n)).eval S p env = some (relationCode (graph 1)) := by
  have hh := Term.eval_mapSet S p Term.atoms
    (Term.orderedPair (Term.var (0 : Fin (n+1))) (Term.var 0)) env rfl
    (fun a => Term.eval_orderedPair S p _ _ _ rfl rfl)
  simpa only [mapSet,identityRelation,elements_ofFinset,Finset.image_image,relationCode,
    graph,pairCode,Function.comp_def,Fin.cons_zero,Equiv.Perm.one_apply] using hh

lemma Term.eval_localPool (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (B : ℕ) (env : Fin n → HF A) :
    (Term.localPool B).eval S p env =
      some (ofFinset ((RelationPools.localPool (A := A) B).image relationCode)) := by
  have hh := Term.eval_mapSet S p (Term.partialPool B) Term.completeRelation env
    (Term.eval_partialPool S p B env) (fun r => Term.eval_completeRelation S p env r)
  have hc := Term.eval_cup S p (Term.identityRelation.singleton) _ env
    (Term.eval_singleton S p _ env (Term.eval_identityRelation S p env)) hh
  convert hc using 1
  congr 2
  simp only [RelationPools.localPool,Finset.image_insert,Hereditary.singleton,elements_ofFinset,
    Finset.singleton_union,Finset.image_image,partialRelations_eq,Function.comp_def,completeHF_tuple]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

structure QuotedTerm (n : ℕ) where
  code : Term n
  meaning : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → HF A
  count : code.wscCount = 0
  correct : ∀ {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A),
    code.eval S p env = some (meaning S env)

structure QuotedFormula (n : ℕ) where
  code : Formula n
  meaning : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → Prop
  count : code.wscCount = 0
  correct : ∀ {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A),
    code.eval S p env = some (decide (meaning S env))

namespace QuotedTerm

variable {n m : ℕ}

def var (j : Fin n) : QuotedTerm n := ⟨.var j,fun _ env => env j,rfl,fun _ _ _ => rfl⟩

def empty : QuotedTerm n := ⟨.empty,fun _ _ => emptyHF,rfl,fun _ _ _ => rfl⟩

def atoms : QuotedTerm n := ⟨.atoms,fun _ _ => ofFinset (Finset.univ.image atom),rfl,fun _ _ _ => rfl⟩

def rename (a : QuotedTerm n) (f : Fin n → Fin m) : QuotedTerm m where
  code := a.code.rename f
  meaning := fun S env => a.meaning S (env ∘ f)
  count := (a.code.rename_count f).trans a.count
  correct S p env := (a.code.eval_rename S p a.count f env).trans (a.correct S p (env ∘ f))

def up (a : QuotedTerm n) : QuotedTerm (n+1) := a.rename Fin.succ

def double (a b : QuotedTerm n) : QuotedTerm n where
  code := .pair a.code b.code
  meaning := fun S env => Hereditary.double (a.meaning S env) (b.meaning S env)
  count := by simp only [Term.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Term.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some]

def union (a : QuotedTerm n) : QuotedTerm n where
  code := .union a.code
  meaning := fun S env => unionHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def unique (a : QuotedTerm n) : QuotedTerm n where
  code := .unique a.code
  meaning := fun S env => uniqueHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def card (a : QuotedTerm n) : QuotedTerm n where
  code := .card a.code
  meaning := fun S env => cardHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def singleton (a : QuotedTerm n) : QuotedTerm n := a.double a

def cup (a b : QuotedTerm n) : QuotedTerm n := (a.double b).union

def pair (a b : QuotedTerm n) : QuotedTerm n := a.singleton.double (a.double b)

end QuotedTerm

namespace QuotedFormula

variable {n m : ℕ}

def rename (a : QuotedFormula n) (f : Fin n → Fin m) : QuotedFormula m where
  code := a.code.rename f
  meaning := fun S env => a.meaning S (env ∘ f)
  count := (a.code.rename_count f).trans a.count
  correct S p env := (a.code.eval_rename S p a.count f env).trans (a.correct S p (env ∘ f))

def up (a : QuotedFormula n) : QuotedFormula (n+1) := a.rename Fin.succ

def eq (a b : QuotedTerm n) : QuotedFormula n where
  code := .equal a.code b.code
  meaning := fun S env => a.meaning S env = b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by
    simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some]
    exact congrArg some (decide_eq_decide.mpr Iff.rfl)

def input (r : Symbol) (a b : QuotedTerm n) : QuotedFormula n where
  code := .input r a.code b.code
  meaning := fun S env => inputHF S r (a.meaning S env) (b.meaning S env) = true
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_eq_true]

def truth : QuotedFormula n := eq .empty .empty

def neg (a : QuotedFormula n) : QuotedFormula n where
  code := .neg a.code
  meaning := fun S env => ¬ a.meaning S env
  count := a.count
  correct S p env := by simp only [Formula.eval,a.correct,Option.map_some,decide_not]

def and (a b : QuotedFormula n) : QuotedFormula n where
  code := .and a.code b.code
  meaning := fun S env => a.meaning S env ∧ b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_and]

def or (a b : QuotedFormula n) : QuotedFormula n where
  code := .or a.code b.code
  meaning := fun S env => a.meaning S env ∨ b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_or]

def imp (a b : QuotedFormula n) : QuotedFormula n := a.neg.or b

def iff (a b : QuotedFormula n) : QuotedFormula n := (a.imp b).and (b.imp a)

def mem (a b : QuotedTerm n) : QuotedFormula n where
  code := .mem a.code b.code
  meaning := fun S env => a.meaning S env ∈ elements (b.meaning S env)
  count := by simp only [Formula.mem,Formula.existsIn,Term.up,Term.rename_count,
    Formula.wscCount,Term.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_mem S p _ _ a.count env (a.correct S p env) (b.correct S p env)]
    exact congrArg some (decide_eq_decide.mpr Iff.rfl)

def existsIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) : QuotedFormula n where
  code := .existsIn r.code a.code
  meaning := fun S env => ∃ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env)
  count := by simp only [Formula.existsIn,Term.wscCount,Formula.wscCount,r.count,a.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_existsIn S p r.code a.code env (r.correct S p env) (fun _ => a.correct S p _)]
    exact congrArg some (decide_eq_decide.mpr (by simp only [decide_eq_true_eq]))

def allIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) : QuotedFormula n where
  code := .allIn r.code a.code
  meaning := fun S env => ∀ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env)
  count := by simp only [Formula.allIn,Formula.existsIn,Term.wscCount,Formula.wscCount,r.count,a.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_allIn S p r.code a.code env (r.correct S p env) (fun _ => a.correct S p _)]
    exact congrArg some (decide_eq_decide.mpr (by simp only [decide_eq_true_eq]))

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def comprehend (r : QuotedTerm n) (body : QuotedTerm (n+1)) (guard : QuotedFormula (n+1)) : QuotedTerm n where
  code := .comprehend body.code r.code guard.code
  meaning := fun S env => ofFinset (((elements (r.meaning S env)).filter
    (fun x => guard.meaning S (Fin.cons x env))).image (fun x => body.meaning S (Fin.cons x env)))
  count := by simp only [Term.wscCount,r.count,body.count,guard.count,Nat.add_zero]
  correct S p env := by
    simpa only [decide_eq_true_eq] using Term.eval_comprehend S p r.code body.code guard.code env
      (r.correct S p env) (fun _ => body.correct S p _) (fun _ => guard.correct S p _)

def map (r : QuotedTerm n) (body : QuotedTerm (n+1)) : QuotedTerm n := r.comprehend body .truth

def bind (r : QuotedTerm n) (body : QuotedTerm (n+1)) : QuotedTerm n := (r.map body).union

def filter (r : QuotedTerm n) (guard : QuotedFormula (n+1)) : QuotedTerm n := r.comprehend (.var 0) guard

def inter (a b : QuotedTerm n) : QuotedTerm n := a.filter (.mem (.var 0) b.up)

def diff (a b : QuotedTerm n) : QuotedTerm n := a.filter (.neg (.mem (.var 0) b.up))

def cond (g : QuotedFormula n) (a b : QuotedTerm n) : QuotedTerm n where
  code := .cond g.code a.code b.code
  meaning := fun S env => if g.meaning S env then a.meaning S env else b.meaning S env
  count := by simp only [Term.cond,Term.cup,Term.when,Term.singleton,Term.up_count,
    Formula.up_count,Term.wscCount,Formula.wscCount,g.count,a.count,b.count,Nat.add_zero]
  correct S p env := by
    simpa only [decide_eq_true_eq] using Term.eval_cond S p g.code a.code b.code
      g.count a.count b.count env (g.correct S p env) (a.correct S p env) (b.correct S p env)

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

namespace QuotedTerm

variable {n : ℕ}

def describe (a : QuotedTerm n)
    (f : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → HF A)
    (h : ∀ {A : Type} [Fintype A] (S : Input A) env, a.meaning S env = f S env) : QuotedTerm n where
  code := a.code
  meaning := f
  count := a.count
  correct S p env := (a.correct S p env).trans (congrArg some (h S env))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_var (j : Fin n) : (var j).meaning S env = env j := rfl

@[simp] lemma meaning_empty : (empty : QuotedTerm n).meaning S env = emptyHF := rfl

@[simp] lemma meaning_atoms : (atoms : QuotedTerm n).meaning S env = stateCode Finset.univ := rfl

@[simp] lemma meaning_up (a : QuotedTerm n) (x : HF A) : a.up.meaning S (Fin.cons x env) = a.meaning S env := rfl

@[simp] lemma meaning_double (a b : QuotedTerm n) : (a.double b).meaning S env = Hereditary.double (a.meaning S env) (b.meaning S env) := rfl

@[simp] lemma meaning_singleton (a : QuotedTerm n) : a.singleton.meaning S env = Hereditary.singleton (a.meaning S env) := by simp [singleton,Hereditary.double,Hereditary.singleton]

@[simp] lemma meaning_pair (a b : QuotedTerm n) : (a.pair b).meaning S env = Hereditary.pair (a.meaning S env) (b.meaning S env) := by simp [pair,Hereditary.pair]

@[simp] lemma meaning_filter (a : QuotedTerm n) (g : QuotedFormula (n+1)) :
    (a.filter g).meaning S env = ofFinset ((elements (a.meaning S env)).filter fun x => g.meaning S (Fin.cons x env)) := by
  simp [filter,comprehend]

@[simp] lemma meaning_map (a : QuotedTerm n) (b : QuotedTerm (n+1)) :
    (a.map b).meaning S env = ofFinset ((elements (a.meaning S env)).image fun x => b.meaning S (Fin.cons x env)) := by
  simp [map,comprehend,QuotedFormula.truth,QuotedFormula.eq]

@[simp] lemma meaning_cup (a b : QuotedTerm n) :
    (a.cup b).meaning S env = ofFinset (elements (a.meaning S env) ∪ elements (b.meaning S env)) := by
  simp [cup,union,Hereditary.double,unionHF]

@[simp] lemma meaning_bind (a : QuotedTerm n) (b : QuotedTerm (n+1)) :
    (a.bind b).meaning S env = ofFinset ((elements (a.meaning S env)).biUnion fun x => elements (b.meaning S (Fin.cons x env))) := by
  simp [bind,union,unionHF,Finset.image_biUnion]

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ}

def describe (a : QuotedFormula n)
    (f : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → Prop)
    (h : ∀ {A : Type} [Fintype A] (S : Input A) env, a.meaning S env ↔ f S env) : QuotedFormula n where
  code := a.code
  meaning := f
  count := a.count
  correct S p env := (a.correct S p env).trans (congrArg some (decide_eq_decide.mpr (h S env)))

def allList : List (QuotedFormula n) → QuotedFormula n
  | [] => truth
  | a::l => a.and (allList l)

def allSymbols (q : Symbol → QuotedFormula n) : QuotedFormula n :=
  allList (Finset.univ.toList.map q)

def link (a b r : QuotedTerm n) : QuotedFormula n := mem (a.pair b) r

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_eq (a b : QuotedTerm n) : (eq a b).meaning S env ↔ a.meaning S env = b.meaning S env := Iff.rfl

@[simp] lemma meaning_input (r : Symbol) (a b : QuotedTerm n) : (input r a b).meaning S env ↔ inputHF S r (a.meaning S env) (b.meaning S env) = true := Iff.rfl

@[simp] lemma meaning_up (a : QuotedFormula n) (x : HF A) : a.up.meaning S (Fin.cons x env) ↔ a.meaning S env := Iff.rfl

@[simp] lemma meaning_mem (a b : QuotedTerm n) : (mem a b).meaning S env ↔ a.meaning S env ∈ elements (b.meaning S env) := Iff.rfl

@[simp] lemma meaning_and (a b : QuotedFormula n) : (a.and b).meaning S env ↔ a.meaning S env ∧ b.meaning S env := Iff.rfl

@[simp] lemma meaning_or (a b : QuotedFormula n) : (a.or b).meaning S env ↔ a.meaning S env ∨ b.meaning S env := Iff.rfl

@[simp] lemma meaning_neg (a : QuotedFormula n) : a.neg.meaning S env ↔ ¬ a.meaning S env := Iff.rfl

@[simp] lemma meaning_imp (a b : QuotedFormula n) : (a.imp b).meaning S env ↔ (a.meaning S env → b.meaning S env) := by simp only [imp,meaning_or,meaning_neg]; tauto

@[simp] lemma meaning_iff (a b : QuotedFormula n) : (a.iff b).meaning S env ↔ (a.meaning S env ↔ b.meaning S env) := by simp [iff,iff_iff_implies_and_implies]

@[simp] lemma meaning_allIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) :
    (allIn r a).meaning S env ↔ ∀ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env) := Iff.rfl

@[simp] lemma meaning_existsIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) :
    (existsIn r a).meaning S env ↔ ∃ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env) := Iff.rfl

@[simp] lemma meaning_allList (l : List (QuotedFormula n)) : (allList l).meaning S env ↔ ∀ q ∈ l, q.meaning S env := by
  induction l with
  | nil => simp [allList,truth,eq]
  | cons q l ih => simp [allList,ih]

@[simp] lemma meaning_allSymbols (q : Symbol → QuotedFormula n) : (allSymbols q).meaning S env ↔ ∀ r, (q r).meaning S env := by
  simp [allSymbols]

@[simp] lemma meaning_link (a b r : QuotedTerm n) : (link a b r).meaning S env ↔ Hereditary.pair (a.meaning S env) (b.meaning S env) ∈ elements (r.meaning S env) := by simp [link]

end QuotedFormula

variable {A : Type}

@[simp] lemma inputHF_atoms (S : Input A) (r : Symbol) (a b : A) :
    inputHF S r (atom a) (atom b) = S.rel r a b := by
  simp [inputHF,atom_injective.eq_iff]

@[simp] lemma pair_mem_relationCode (a b : A) (r : Relation A) :
    Hereditary.pair (atom a) (atom b) ∈ elements (relationCode r) ↔ (a,b) ∈ r := by
  change pairCode (a,b) ∈ elements (relationCode r) ↔ _
  simp [relationCode]

@[simp] lemma all_stateCode (s : Finset A) (P : HF A → Prop) :
    (∀ x ∈ elements (stateCode s), P x) ↔ ∀ a ∈ s, P (atom a) := by simp [stateCode]

@[simp] lemma exists_stateCode (s : Finset A) (P : HF A → Prop) :
    (∃ x ∈ elements (stateCode s), P x) ↔ ∃ a ∈ s, P (atom a) := by simp [stateCode]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

@[simp] lemma fin_cons_two {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+2) → X) : (Fin.cons x f : Fin (n+2+1) → X) 2 = f 1 := rfl

@[simp] lemma fin_cons_three {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+3) → X) : (Fin.cons x f : Fin (n+3+1) → X) 3 = f 2 := rfl

@[simp] lemma fin_cons_four {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+4) → X) : (Fin.cons x f : Fin (n+4+1) → X) 4 = f 3 := rfl

@[simp] lemma fin_cons_five {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+5) → X) : (Fin.cons x f : Fin (n+5+1) → X) 5 = f 4 := rfl

namespace QuotedTerm

variable {n : ℕ}

def atomFilter (q : QuotedFormula (n+1)) : QuotedTerm n :=
  (atoms.filter q).describe
    (fun S env => stateCode (Finset.univ.filter fun a => q.meaning S (Fin.cons (atom a) env))) (by
      intro A _ S env
      simp only [meaning_filter,meaning_atoms,stateCode,elements_ofFinset]
      apply ofFinset_inj.mpr
      ext x
      simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
      aesop)

@[simp] lemma meaning_atomFilter {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)
    (q : QuotedFormula (n+1)) :
    (atomFilter q).meaning S env = stateCode (Finset.univ.filter fun a => q.meaning S (Fin.cons (atom a) env)) := rfl

def relation (q : QuotedFormula (n+2)) : QuotedTerm n :=
  (atoms.bind (atoms.comprehend ((var 1).pair (var 0)) q)).describe
    (fun S env => relationCode (Finset.univ.filter fun ab =>
      q.meaning S (Fin.cons (atom ab.2) (Fin.cons (atom ab.1) env)))) (by
      intro A _ S env
      simp only [meaning_bind,meaning_atoms,comprehend,meaning_pair,meaning_var,
        relationCode,stateCode,elements_ofFinset]
      apply ofFinset_inj.mpr
      ext x
      simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
        true_and,Prod.exists]
      constructor
      · rintro ⟨a,⟨a',rfl⟩,b,⟨⟨b',rfl⟩,hq⟩,rfl⟩
        exact ⟨a',b',hq,rfl⟩
      · rintro ⟨a,b,hq,rfl⟩
        exact ⟨atom a,⟨a,rfl⟩,atom b,⟨⟨b,rfl⟩,hq⟩,rfl⟩)

@[simp] lemma meaning_relation {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)
    (q : QuotedFormula (n+2)) :
    (relation q).meaning S env = relationCode (Finset.univ.filter fun ab =>
      q.meaning S (Fin.cons (atom ab.2) (Fin.cons (atom ab.1) env))) := rfl

def edgeAtoms : QuotedTerm n := atomFilter (.input .Ed (.var 0) (.var 0))

def configAtoms : QuotedTerm n := atomFilter (.input .Cf (.var 0) (.var 0))

def edgeRow (a : QuotedTerm n) : QuotedTerm n := edgeAtoms.filter (.input .EB a.up (.var 0))

def vertexRow (a : QuotedTerm n) : QuotedTerm n := configAtoms.filter (.input .VB a.up (.var 0))

def edgeBlocks : QuotedTerm n := edgeAtoms.map (edgeRow (.var 0))

def vertexBlocks : QuotedTerm n := configAtoms.map (vertexRow (.var 0))

def blocks : QuotedTerm n := edgeBlocks.cup vertexBlocks

def identity : QuotedTerm n where
  code := .identityRelation
  meaning := fun _ _ => relationCode (graph 1)
  count := Term.identityRelation_count
  correct S p env := Term.eval_identityRelation S p env

def localRelations (B : ℕ) : QuotedTerm n where
  code := .localPool B
  meaning := fun _ _ => ofFinset ((localPool B).image relationCode)
  count := Term.localPool_count B
  correct S p env := Term.eval_localPool S p B env

def composition (l c : QuotedTerm n) : QuotedTerm n := relation
  (.existsIn .atoms ((QuotedFormula.link (.var 2) (.var 0) l.up.up.up).and
    (.link (.var 0) (.var 1) c.up.up.up)))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_edgeAtoms : (edgeAtoms : QuotedTerm n).meaning S env = stateCode (WitnessedChoice.edgeAtoms S) := by
  simp [edgeAtoms,WitnessedChoice.edgeAtoms]

@[simp] lemma meaning_configAtoms : (configAtoms : QuotedTerm n).meaning S env = stateCode (WitnessedChoice.configAtoms S) := by
  simp [configAtoms,WitnessedChoice.configAtoms]

lemma meaning_edgeRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (edgeRow a).meaning S env = stateCode (WitnessedChoice.edgeRow S x) := by
  simp only [edgeRow,meaning_filter,meaning_edgeAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.edgeRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

lemma meaning_vertexRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (vertexRow a).meaning S env = stateCode (WitnessedChoice.vertexRow S x) := by
  simp only [vertexRow,meaning_filter,meaning_configAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.vertexRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

@[simp] lemma meaning_edgeBlocks : (edgeBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.edgeBlocks S).image stateCode) := by
  simp only [edgeBlocks,meaning_map,meaning_edgeAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.edgeBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_edgeRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_vertexBlocks : (vertexBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.vertexBlocks S).image stateCode) := by
  simp only [vertexBlocks,meaning_map,meaning_configAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.vertexBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_vertexRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_blocks : (blocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.blocks S).image stateCode) := by
  simp only [blocks,meaning_cup,meaning_edgeBlocks,meaning_vertexBlocks,elements_ofFinset,WitnessedChoice.blocks]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image]
  aesop

lemma meaning_composition (l c : QuotedTerm n) (r t : Relation A)
    (hl : l.meaning S env = relationCode r) (hc : c.meaning S env = relationCode t) :
    (composition l c).meaning S env = relationCode (compose r t) := by
  simp only [composition,meaning_relation,QuotedFormula.meaning_existsIn,meaning_atoms,
    exists_stateCode,Finset.mem_univ,true_and,QuotedFormula.meaning_and,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,
    fin_cons_two,meaning_up,hl,hc,pair_mem_relationCode]
  rfl

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

def FunctionalOnto (r : Relation A) : Prop :=
  (∀ a, ∃! b, (a,b) ∈ r) ∧ ∀ b, ∃ a, (a,b) ∈ r

lemma functionalOnto_iff (r : Relation A) : FunctionalOnto r ↔ ∃ g : Equiv.Perm A, r = graph g := by
  constructor
  · intro h
    let f : A → A := fun a => (h.1 a).choose
    have hf (a : A) : (a,f a) ∈ r ∧ ∀ b, (a,b) ∈ r → b = f a := (h.1 a).choose_spec
    have hs : Function.Surjective f := by
      intro b
      obtain ⟨a,hab⟩ := h.2 b
      exact ⟨a,((hf a).2 b hab).symm⟩
    let g : Equiv.Perm A := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
    refine ⟨g,?_⟩
    ext ⟨a,b⟩
    simp only [mem_graph]
    constructor
    · intro hab
      exact ((hf a).2 b hab).symm
    · intro he
      rw [←he]
      exact (hf a).1
  · rintro ⟨g,rfl⟩
    constructor
    · intro a
      exact ⟨g a,by simp,fun b hb => (mem_graph g a b).mp hb |>.symm⟩
    · intro b
      exact ⟨g.symm b,by simp⟩

def RawFilter (S : Input A) (x : Finset A) (r : Relation A) : Prop :=
  FunctionalOnto r ∧
  (∀ R a a' b b', (a,b) ∈ r → (a',b') ∈ r → S.rel R a a' = S.rel R b b') ∧
  (∀ u ∈ blocks S, ∀ a ∈ u, ∀ b, (a,b) ∈ r → b ∈ u) ∧
  ∀ a ∈ x, (a,a) ∈ r

lemma rawFilter_graph (S : Input A) (x : Finset A) (g : Equiv.Perm A) :
    RawFilter S x (graph g) ↔ PoolFilter S x g := by
  constructor
  · rintro ⟨_,hR,hB,hx⟩
    refine ⟨?_,?_,?_⟩
    · intro R a b
      exact (hR R a b (g a) (g b) (by simp) (by simp)).symm
    · intro u hu
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
        exact hB u hu a ha (g a) (by simp)
      · rw [Finset.card_image_of_injective _ g.injective]
    · intro a ha
      exact (mem_graph g a a).mp (hx a ha)
  · rintro ⟨hR,hB,hx⟩
    refine ⟨(functionalOnto_iff _).mpr ⟨g,rfl⟩,?_,?_,?_⟩
    · intro R a a' b b' hab ha'b'
      rw [←(mem_graph g a b).mp hab,←(mem_graph g a' b').mp ha'b']
      exact (hR R a a').symm
    · intro u hu a ha b hab
      rw [←(mem_graph g a b).mp hab,←hB u hu]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    · intro a ha
      exact (mem_graph g a a).mpr (hx a ha)

lemma rawFilter_iff (S : Input A) (x : Finset A) (r : Relation A) :
    RawFilter S x r ↔ ∃ g : Equiv.Perm A, r = graph g ∧ PoolFilter S x g := by
  constructor
  · intro h
    obtain ⟨g,rfl⟩ := (functionalOnto_iff r).mp h.1
    exact ⟨g,rfl,(rawFilter_graph S x g).mp h⟩
  · rintro ⟨g,rfl,hg⟩
    exact (rawFilter_graph S x g).mpr hg

namespace QuotedFormula

variable {n : ℕ}

def functional (r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms (existsIn .atoms
    ((link (.var 1) (.var 0) r.up.up).and
      (allIn .atoms ((link (.var 2) (.var 0) r.up.up.up).imp (eq (.var 0) (.var 1))))))

def onto (r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms (existsIn .atoms (link (.var 0) (.var 1) r.up.up))

def preserves (r : QuotedTerm n) : QuotedFormula n := allSymbols fun R =>
  allIn .atoms (allIn .atoms (allIn .atoms (allIn .atoms
    (((link (.var 3) (.var 1) r.up.up.up.up).and
      (link (.var 2) (.var 0) r.up.up.up.up)).imp
      ((input R (.var 3) (.var 2)).iff (input R (.var 1) (.var 0)))))))

def fixesBlocks (r : QuotedTerm n) : QuotedFormula n :=
  allIn .blocks (allIn (.var 0) (allIn .atoms
    ((link (.var 1) (.var 0) r.up.up.up).imp (mem (.var 0) (.var 2)))))

def fixesState (x r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms ((mem (.var 0) x.up).imp (link (.var 0) (.var 0) r.up))

def filter (x r : QuotedTerm n) : QuotedFormula n :=
  (functional r).and ((onto r).and ((preserves r).and ((fixesBlocks r).and (fixesState x r))))

variable (S : Input A) (env : Fin n → HF A)

lemma meaning_functional (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (functional r).meaning S env ↔ ∀ a, ∃! b, (a,b) ∈ R := by
  simp [functional,hr,ExistsUnique,atom_injective.eq_iff,pairCode]
  constructor
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    exact ⟨b,hb,fun c hc => hu c a c hc rfl rfl⟩
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    refine ⟨b,hb,?_⟩
    rintro c d e hc rfl rfl
    exact hu e hc

lemma meaning_onto (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (onto r).meaning S env ↔ ∀ b, ∃ a, (a,b) ∈ R := by
  simp [onto,hr,pairCode,atom_injective.eq_iff]

lemma meaning_preserves (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (preserves r).meaning S env ↔ ∀ s a a' b b', (a,b) ∈ R → (a',b') ∈ R → S.rel s a a' = S.rel s b b' := by
  simp [preserves,hr,Bool.coe_iff_coe,and_imp,pairCode,atom_injective.eq_iff]
  aesop

lemma meaning_fixesBlocks (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (fixesBlocks r).meaning S env ↔ ∀ u ∈ blocks S, ∀ a ∈ u, ∀ b, (a,b) ∈ R → b ∈ u := by
  simp [fixesBlocks,hr,stateCode,atom_injective.eq_iff,pairCode]
  aesop

lemma meaning_fixesState (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (fixesState x r).meaning S env ↔ ∀ a ∈ X, (a,a) ∈ R := by
  simp [fixesState,hx,hr,stateCode,atom_injective.eq_iff,pairCode]

lemma meaning_filter (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (filter x r).meaning S env ↔ RawFilter S X R := by
  rw [filter,meaning_and,meaning_and,meaning_and,meaning_and,
    meaning_functional S env r R hr,meaning_onto S env r R hr,
    meaning_preserves S env r R hr,meaning_fixesBlocks S env r R hr,
    meaning_fixesState S env x r X R hx hr]
  simp only [RawFilter,FunctionalOnto,and_assoc]

end QuotedFormula

end

end WitnessedChoice.BGS

end OAI
