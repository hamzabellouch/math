import OAI.Combinatorics.ListHadwiger.Stage

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure Segment {V : Type} (G : SimpleGraph V) (A B : Finset V) where
  left : ↥A
  walk : Σ v, G.Path left.val v
  right_mem : walk.1∈B

structure Unpaired {V : Type} (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  segment : Fin n → Segment G A B
  disjoint : ∀ i j, i≠j → Disjoint {v | v∈(segment i).walk.2.val.support}
    {v | v∈(segment j).walk.2.val.support}

namespace Unpaired
variable {V : Type} {G : SimpleGraph V} {A B : Finset V} {n : ℕ}

def totalLength (D : Unpaired G A B n) : ℕ := ∑ i, (D.segment i).walk.2.val.length

def Minimal (D : Unpaired G A B n) : Prop := ∀ E : Unpaired G A B n,
  D.totalLength ≤ E.totalLength

lemma exists_minimal (h : Nonempty (Unpaired G A B n)) :
    ∃ D : Unpaired G A B n, D.Minimal := by
  obtain ⟨D⟩ := h
  have hex : ∃ m : ℕ, ∃ E : Unpaired G A B n, E.totalLength=m := ⟨D.totalLength,D,rfl⟩
  obtain ⟨E,hE⟩ := Nat.find_spec hex
  exact ⟨E,fun F => hE ▸ Nat.find_min' hex ⟨F,rfl⟩⟩

lemma source_injective (D : Unpaired G A B n) :
    Function.Injective (fun i => (D.segment i).left) := by
  intro i j hij
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint i j hne)
    (D.segment i).walk.2.val.start_mem_support
    (by simpa only [hij,Set.mem_ofPred_eq] using (D.segment j).walk.2.val.start_mem_support)

lemma target_injective (D : Unpaired G A B n) :
    Function.Injective (fun i => (D.segment i).walk.1) := by
  intro i j hij
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint i j hne)
    (D.segment i).walk.2.val.end_mem_support
    (by simpa only [hij,Set.mem_ofPred_eq] using (D.segment j).walk.2.val.end_mem_support)

def replace (D : Unpaired G A B n) (i : Fin n) (P : Segment G A B)
    (hP : ∀ v, v∈P.walk.2.val.support → v∈(D.segment i).walk.2.val.support) :
    Unpaired G A B n where
  segment := Function.update D.segment i P
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v hva hvb
    have hs (j : Fin n) : {v | v∈(Function.update D.segment i P j).walk.2.val.support} ⊆
        {v | v∈(D.segment j).walk.2.val.support} := by
      by_cases hj : j=i
      · subst j
        rw [Function.update_self]
        exact hP
      · rw [Function.update_of_ne hj]
    exact Set.disjoint_left.mp (D.disjoint a b hab) (hs a hva) (hs b hvb)

lemma replace_shorter (D : Unpaired G A B n) (i : Fin n) (P : Segment G A B)
    (hP : ∀ v, v∈P.walk.2.val.support → v∈(D.segment i).walk.2.val.support)
    (hlen : P.walk.2.val.length < (D.segment i).walk.2.val.length) :
    (D.replace i P hP).totalLength < D.totalLength := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j=i
    · subst j
      change (Function.update D.segment i P i).walk.2.val.length ≤ (D.segment i).walk.2.val.length
      rw [Function.update_self]
      exact hlen.le
    · change (Function.update D.segment i P j).walk.2.val.length ≤ (D.segment j).walk.2.val.length
      rw [Function.update_of_ne hj]
  · refine ⟨i,mem_univ _,?_⟩
    change (Function.update D.segment i P i).walk.2.val.length < (D.segment i).walk.2.val.length
    rw [Function.update_self]
    exact hlen

lemma Minimal.source_only [DecidableEq V] {D : Unpaired G A B n} (hD : D.Minimal)
    (i : Fin n) (v : V) (hv : v∈(D.segment i).walk.2.val.support) (ha : v∈A) :
    v=(D.segment i).left.val := by
  by_contra hn
  let P : Segment G A B := ⟨⟨v,ha⟩,⟨(D.segment i).walk.1,
    ⟨(D.segment i).walk.2.val.dropUntil v hv,(D.segment i).walk.2.property.dropUntil hv⟩⟩,
    (D.segment i).right_mem⟩
  have hp (w : V) : w∈P.walk.2.val.support → w∈(D.segment i).walk.2.val.support :=
    fun hw => (D.segment i).walk.2.val.support_dropUntil_subset_support hv hw
  have hs := D.replace_shorter i P hp (Walk.length_dropUntil_lt_length hv hn)
  exact (not_lt_of_ge (hD _)) hs

lemma Minimal.target_only [DecidableEq V] {D : Unpaired G A B n} (hD : D.Minimal)
    (i : Fin n) (v : V) (hv : v∈(D.segment i).walk.2.val.support) (hb : v∈B) :
    v=(D.segment i).walk.1 := by
  by_contra hn
  let P : Segment G A B := ⟨(D.segment i).left,⟨v,
    ⟨(D.segment i).walk.2.val.takeUntil v hv,(D.segment i).walk.2.property.takeUntil hv⟩⟩,hb⟩
  have hp (w : V) : w∈P.walk.2.val.support → w∈(D.segment i).walk.2.val.support :=
    fun hw => (D.segment i).walk.2.val.support_takeUntil_subset_support hv hw
  have hs := D.replace_shorter i P hp (Walk.length_takeUntil_lt_length hv hn)
  exact (not_lt_of_ge (hD _)) hs

def routing (D : Unpaired G A B n) : BagRouting G (fun i => (D.segment i).left.val)
    (fun b : ↥B => {b.val}) where
  paths i := (D.segment i).walk
  bag i := ⟨(D.segment i).walk.1,(D.segment i).right_mem⟩
  bag_injective _ _ h := D.target_injective (congrArg Subtype.val h)
  endpoint_mem _ := rfl
  overlap i j hij _ hvi hvj := (Set.disjoint_left.mp (D.disjoint i j hij) hvi hvj).elim

lemma routing_minimal {D : Unpaired G A B n} (hD : D.Minimal) : D.routing.Minimal := by
  intro E
  let F : Unpaired G A B n := {
    segment := fun i => ⟨(D.segment i).left,E.paths i,
      (E.endpoint_mem i) ▸ (E.bag i).property⟩
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      have he := E.overlap i j hij v hvi hvj
      exact hij (D.source_injective (Subtype.ext (he.1.symm.trans he.2))) }
  exact hD F

def ofFullPacking {A₀ : Finset V} (P : PathPacking.FullPacking G A₀ B)
    (hA : A₀ ⊆ A) (e : Fin n ≃ ↥A₀) : Unpaired G A B n where
  segment i := ⟨⟨(e i).val,hA (e i).property⟩,⟨(P.target (e i)).val,P.route (e i)⟩,
    (P.target (e i)).property⟩
  disjoint i j hij := P.disjoint (e i) (e j) (fun h => hij (e.injective h))

end Unpaired
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def under (U A : Finset V) : Finset ↥(↑U : Set V) :=
  univ.filter (fun v => v.val∈A)

omit [Fintype V] in
@[simp] lemma mem_under {U A : Finset V} (v : ↥(↑U : Set V)) :
    v∈under U A ↔ v.val∈A := by simp [under]

omit [Fintype V] in
lemma under_image {U A : Finset V} (hA : A⊆U) : (under U A).image Subtype.val=A := by
  ext v
  simp only [mem_image,mem_under]
  constructor
  · rintro ⟨w,hw,rfl⟩; exact hw
  · intro hv; exact ⟨⟨v,hA hv⟩,hv,rfl⟩

omit [Fintype V] in
lemma under_card {U A : Finset V} (hA : A⊆U) : (under U A).card=A.card := by
  calc
    _ = ((under U A).image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card (under_image hA)

omit [Fintype V] in
lemma under_disjoint {U A B : Finset V} (h : Disjoint A B) :
    Disjoint (under U A) (under U B) := by
  apply disjoint_left.mpr
  intro v hv hw
  exact disjoint_left.mp h (mem_under v |>.mp hv) (mem_under v |>.mp hw)

omit [Fintype V] in
lemma under_connected (G : SimpleGraph V) {U A : Finset V} {k : ℕ}
    (hA : A⊆U) (hc : KConnectedOn G A k) :
    KConnectedOn (G.induce (↑U : Set V)) (under U A) k := by
  classical
  refine ⟨by simpa only [under_card hA] using hc.1,?_⟩
  intro X hX hx
  let Z := X.image Subtype.val
  have hZA : Z⊆A := by
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_under w).mp (hX hw)
  have hZk : Z.card<k := by
    simpa only [Z,card_image_of_injective _ Subtype.val_injective] using hx
  have hcon := hc.2 Z hZA hZk
  let f : G.induce (↑(A\Z) : Set V) →g
      (G.induce (↑U : Set V)).induce (↑(under U A\X) : Set ↥(↑U : Set V)) := {
    toFun := fun v => ⟨⟨v.val,hA (mem_sdiff.mp v.property).1⟩,
      mem_sdiff.mpr ⟨(mem_under _).mpr (mem_sdiff.mp v.property).1,
        fun hv => (mem_sdiff.mp v.property).2 (mem_image.mpr ⟨_,hv,rfl⟩)⟩⟩
    map_rel' := fun h => h }
  apply hcon.map f
  intro w
  have hw : w.val.val∈A\Z := by
    refine mem_sdiff.mpr ⟨(mem_under _).mp (mem_sdiff.mp w.property).1,?_⟩
    intro hz
    obtain ⟨a,ha,he⟩ := mem_image.mp hz
    have heq : a=w.val := Subtype.ext he
    exact (mem_sdiff.mp w.property).2 (heq ▸ ha)
  exact ⟨⟨w.val.val,hw⟩,rfl⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint.System
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

noncomputable def ofMinimal (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) : System G where
  domain := U
  n := Fintype.card I
  source := s ∘ (Fintype.equivFin I).symm
  target := T
  routes := D.reindex (Fintype.equivFin I).symm
  minimal := BagRouting.minimal_reindex hD _

lemma ofMinimal_starts (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) :
    (ofMinimal U s T D hD).starts=univ.image (fun i => (s i).val) := by
  change univ.image (fun i : Fin (Fintype.card I) => (s ((Fintype.equivFin I).symm i)).val) = _
  ext v
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨_,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨Fintype.equivFin I i,by simpa using hi⟩

lemma ofMinimal_ends (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) : (ofMinimal U s T D hD).ends ⊆ T.image Subtype.val := by
  rintro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  have he := D.endpoint_mem ((Fintype.equivFin I).symm i)
  exact mem_image.mpr ⟨_,(D.bag _).property,congrArg Subtype.val he.symm⟩

lemma ofMinimal_injective (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) (hs : Function.Injective s) :
    Function.Injective (ofMinimal U s T D hD).source :=
  hs.comp (Fintype.equivFin I).symm.injective

noncomputable def route (S : System G) (i : Fin S.n) :
    G.Path (S.source i).val (S.routes.paths i).1.val :=
  ⟨(S.routes.paths i).2.val.map ⟨Subtype.val,fun h => h⟩,
    (S.routes.paths i).2.property.map Subtype.val_injective⟩

lemma mem_route (S : System G) (i : Fin S.n) (v : V) :
    v∈(S.route i).val.support ↔ v∈S.path i := by
  simp only [route,path,SimpleGraph.Walk.support_map,List.mem_map,mem_image,List.mem_toFinset]
  rfl

noncomputable def empty (U : Finset V) : System G where
  domain := U
  n := 0
  source := Fin.elim0
  target := ∅
  routes := {
    paths := by intro i; exact Fin.elim0 i
    bag := Fin.elim0
    bag_injective := by intro i; exact Fin.elim0 i
    endpoint_mem := by intro i; exact Fin.elim0 i
    overlap := by intro i; exact Fin.elim0 i }
  minimal := by intro E; simp [BagRouting.totalLength]

@[simp] lemma empty_used (U : Finset V) : (empty (G:=G) U).used=∅ := by
  ext v
  simp [mem_used,empty]

@[simp] lemma empty_starts (U : Finset V) : (empty (G:=G) U).starts=∅ := by
  ext v
  simp only [starts,mem_image,Finset.notMem_empty,iff_false]
  rintro ⟨i,_,_⟩
  exact Fin.elim0 i

@[simp] lemma empty_ends (U : Finset V) : (empty (G:=G) U).ends=∅ := by
  ext v
  simp only [ends,mem_image,Finset.notMem_empty,iff_false]
  rintro ⟨i,_,_⟩
  exact Fin.elim0 i

end LinearListHadwiger.Footprint.System

namespace LinearListHadwiger.DoublePacking
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}

noncomputable def ofMinimal
    (D : BagRouting G (fun i : ↥A×Bool => i.1.val) (fun b : ↥B => {b.val}))
    (hD : D.Minimal) (hAB : Disjoint A B) : DoublePacking G A B where
  target := D.bag
  target_injective := D.bag_injective
  route i := ⟨(D.paths i).2.val.copy rfl (Set.mem_singleton_iff.mp (D.endpoint_mem i)),
    by rw [SimpleGraph.Walk.isPath_copy]; exact (D.paths i).2.property⟩
  source_only i v hv ha := by
    rw [SimpleGraph.Walk.support_copy] at hv
    by_contra hn
    let j : ↥A×Bool := (⟨v,ha⟩,false)
    have hij : i≠j := fun he => hn (congrArg (fun x : ↥A×Bool => x.1.val) he).symm
    exact hn (D.overlap i j hij v hv (D.paths j).2.val.start_mem_support).1
  target_only i v hv hb := by
    rw [SimpleGraph.Walk.support_copy] at hv
    exact (BagRouting.minimal_target_only hD
      (fun i hi => Finset.disjoint_left.mp hAB i.1.property hi) i v hv hb).trans (Set.mem_singleton_iff.mp (D.endpoint_mem i))
  overlap i j hij v hv hw := by
    rw [SimpleGraph.Walk.support_copy] at hv hw
    exact D.overlap i j hij v hv hw

@[simp] lemma ofMinimal_support
    (D : BagRouting G (fun i : ↥A×Bool => i.1.val) (fun b : ↥B => {b.val}))
    (hD : D.Minimal) (hAB : Disjoint A B) (i : ↥A×Bool) :
    ((ofMinimal D hD hAB).route i).val.support=(D.paths i).2.val.support := by
  simp only [ofMinimal,SimpleGraph.Walk.support_copy]

def liftIndex {U A : Finset V} (hA : A⊆U) (i : ↥A×Bool) : ↥(Stage.under U A)×Bool :=
  (⟨⟨i.1.val,hA i.1.property⟩,Stage.mem_under _ |>.mpr i.1.property⟩,i.2)

lemma liftIndex_injective {U A : Finset V} (hA : A⊆U) :
    Function.Injective (liftIndex hA) := by
  intro i j he
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun x : ↥(Stage.under U A)×Bool => x.1.val.val) he)
  · exact congrArg (fun x : ↥(Stage.under U A)×Bool => x.2) he

noncomputable def lift {U A B : Finset V} (hA : A⊆U) (_hB : B⊆U)
    (P : DoublePacking (G.induce (↑U : Set V)) (Stage.under U A) (Stage.under U B)) :
    DoublePacking G A B where
  target i := ⟨(P.target (liftIndex hA i)).val.val,
    (Stage.mem_under _).mp (P.target (liftIndex hA i)).property⟩
  target_injective := by
    intro i j he
    apply liftIndex_injective hA
    apply P.target_injective
    have hh : (P.target (liftIndex hA i)).val.val = (P.target (liftIndex hA j)).val.val :=
      congrArg (fun x : ↥B => x.val) he
    exact Subtype.ext (Subtype.ext hh)
  route i := ⟨(P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩,
    (P.route (liftIndex hA i)).property.map Subtype.val_injective⟩
  source_only i v hv ha := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact congrArg Subtype.val (P.source_only _ w hw ((Stage.mem_under _).mpr ha))
  target_only i v hv hb := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact congrArg Subtype.val (P.target_only _ w hw ((Stage.mem_under _).mpr hb))
  overlap i j hij v hv hw := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    change v∈((P.route (liftIndex hA j)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hw
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv hw
    obtain ⟨a,ha,rfl⟩ := hv
    obtain ⟨b,hb,he⟩ := hw
    have hab : b=a := Subtype.ext he
    subst b
    have hh := P.overlap _ _ (fun he => hij (liftIndex_injective hA he)) a ha hb
    exact ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩

lemma mem_lift_route {U A B : Finset V} (hA : A⊆U) (hB : B⊆U)
    (P : DoublePacking (G.induce (↑U : Set V)) (Stage.under U A) (Stage.under U B))
    (i : ↥A×Bool) (v : V) :
    v∈((P.lift hA hB).route i).val.support ↔
      ∃ w : ↥(↑U : Set V), w∈(P.route (liftIndex hA i)).val.support ∧ w.val=v := by
  change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support ↔ _
  rw [SimpleGraph.Walk.support_map,List.mem_map]
  rfl

theorem in_region [Fintype V] (S A B : Finset V) (hA : A⊆S) (hB : B⊆S)
    (hAB : Disjoint A B) (hc : KConnectedOn G S (2*A.card)) (hb : 2*A.card≤B.card) :
    Nonempty (DoublePacking G A B) := by
  have hconn : KConnectedOn (G.induce (↑S : Set V)) univ (2*(Stage.under S A).card) := by
    have hh := Stage.under_connected G (U:=S) (A:=S) (subset_refl S) hc
    have he : Stage.under S S=univ := by ext v; simp [Stage.under]
    simpa only [he,Stage.under_card hA] using hh
  obtain ⟨P⟩ := double_packing (G.induce (↑S : Set V)) (Stage.under S A) (Stage.under S B)
    (Stage.under_disjoint hAB) hconn (by simpa only [Stage.under_card hA,Stage.under_card hB] using hb)
  exact ⟨P.lift hA hB⟩

end LinearListHadwiger.DoublePacking

namespace LinearListHadwiger.Footprint.System
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

lemma mem_ofMinimal_used (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) (v : V) :
    v∈(ofMinimal U s T D hD).used ↔
      ∃ i w, w∈(D.paths i).2.val.support ∧ w.val=v := by
  rw [mem_used]
  simp only [path,ofMinimal,BagRouting.reindex,mem_image]
  constructor
  · rintro ⟨i,w,hw,he⟩; exact ⟨_,w,List.mem_toFinset.mp hw,he⟩
  · rintro ⟨i,w,hw,he⟩
    refine ⟨Fintype.equivFin I i,w,?_,he⟩
    change w∈(D.paths ((Fintype.equivFin I).symm ((Fintype.equivFin I) i))).2.val.support.toFinset
    apply List.mem_toFinset.mpr
    have heq := congrArg (fun j : I => (D.paths j).2.val.support)
      ((Fintype.equivFin I).symm_apply_apply i)
    exact heq.symm ▸ hw

end LinearListHadwiger.Footprint.System

end OAI
