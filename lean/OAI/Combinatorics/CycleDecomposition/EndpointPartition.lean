import OAI.Combinatorics.CycleDecomposition.PathDeletion

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    convert hc'.trans hb using 1

    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

theorem lovasz_theorem : MissingLovaszTheorem :=
  fun _ G => lovasz_path_cycle_partition G

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

theorem endpoint_theorem : MissingEndpointTheorem :=
  fun _ G => endpoint_path_partition G

end
end ErdosGallai

end
end
end

end OAI
