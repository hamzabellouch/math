import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Mixed

namespace OAI

namespace LargeIndependentSets

section
open scoped Classical

namespace Graph
noncomputable def enumeration_to_simple {W : Type} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ} (hn : 0<n) (e : Fin n ≃ W) :
    Renaming (ofEnumeration H hn e) (ofSimple H) where
  equiv := e.trans (Fintype.equivFin W)
  adj_eq i j := by
    simp only [ofEnumeration,ofSimple,decide_eq_decide]
    change H.Adj (e i) (e j) ↔
      H.Adj ((Fintype.equivFin W).symm ((Fintype.equivFin W) (e i)))
        ((Fintype.equivFin W).symm ((Fintype.equivFin W) (e j)))
    simp

end Graph

attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq
namespace SamplerParameters
noncomputable def decisionOutput_renaming (p : SamplerParameters) (q : ℕ) (hq : 0<q)
    {U V L R C : Type} [Fintype L] [Fintype R] [Fintype C] [Nonempty C]
    (lc : LabelCoverData U V L R C) [DecidableRel (p.graph lc).Adj]
    [Decidable (p.CliqueTest lc)] {t : ℕ} (ht : 0<t) (ev : Fin t ≃ p.Vertices L R C) :
    Graph.Renaming
      (if p.CliqueTest lc then Graph.clique q hq else Graph.ofEnumeration (p.graph lc) ht ev)
      (p.output q hq lc) := by
  by_cases hc : p.CliqueTest lc
  · rw [output,ite_eq_left hc,ite_eq_left hc]
    exact ⟨Equiv.refl _,fun _ _ => rfl⟩
  · rw [output,ite_eq_right hc,ite_eq_right hc]
    exact @Graph.enumeration_to_simple (p.Vertices L R C) inferInstance inferInstance
      (p.graph lc) inferInstance t ht ev

variable (p : SamplerParameters) (q : ℕ) (hq : 0<q)
    {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    [DecidableEq (p.Vertices L R C)] [Nonempty C]
    (lc : LabelCoverData U V L R C) {N t : ℕ} (ht : 0<t)
    (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k))
    (ev : Fin t ≃ p.Vertices L R C)

omit [Nonempty C] in
lemma enumeratedGraph_eq : p.enumeratedGraph lc ht eg ev =
    @Graph.ofEnumeration _ (p.graph lc) (p.graphAdjDecidable lc eg) _ ht ev := rfl

noncomputable def enumeratedOutput_renaming :
    Graph.Renaming (p.enumeratedOutput q hq lc ht eg ev) (p.output q hq lc) := by
  letI := p.graphAdjDecidable lc eg
  letI := p.cliqueDecidable lc eg
  exact p.decisionOutput_renaming q hq lc ht ev

lemma enumeratedOutput_complete (ℓ : U → L) (ρ : V → R) (h : lc.Satisfied ℓ ρ) :
    (p.enumeratedOutput q hq lc ht eg ev).ThreeColorable :=
  (p.enumeratedOutput_renaming q hq lc ht eg ev).symm.colorable (p.output_complete q hq lc ℓ ρ h)

omit [Nonempty C] in
lemma enumeratedOutput_size_le :
    (p.enumeratedOutput q hq lc ht eg ev).vertices ≤ max q t := by
  unfold enumeratedOutput
  split
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma enumeratedOutput_size_eq :
    (p.enumeratedOutput q hq lc ht eg ev).vertices = (p.output q hq lc).vertices :=
  (p.enumeratedOutput_renaming q hq lc ht eg ev).vertices_eq

end SamplerParameters

theorem executable_finite_graph_reduction {δ : ℝ} (hδ : 0<δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, ∃ q : ℕ, ∃ hq : 0<q,
    0<σ ∧ σ<1 ∧
    ∀ (U V L R C : Type) [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
      [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
      [DecidableEq (p.Vertices L R C)] [Nonempty L] [Nonempty R] [Nonempty C]
      (lc : LabelCoverData U V L R C) {N t : ℕ} (ht : 0<t)
      (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k))
      (ev : Fin t ≃ p.Vertices L R C),
    ((∃ ℓ ρ, lc.Satisfied ℓ ρ) → (p.enumeratedOutput q hq lc ht eg ev).ThreeColorable) ∧
    (lc.Sound (σ:ℝ) → ((p.enumeratedOutput q hq lc ht eg ev).independenceNumber : ℝ) <
      δ*(p.enumeratedOutput q hq lc ht eg ev).vertices) := by
  obtain ⟨p,σ,q,hq,hσ,hσ1,H⟩ := finite_graph_reduction hδ
  refine ⟨p,σ,q,hq,hσ,hσ1,?_⟩
  intro U V L R C _ _ _ _ _ _ _ _ _ _ _ _ _ lc N t ht eg ev
  have he := (p.enumeratedOutput_renaming q hq lc ht eg ev).symm
  exact ⟨fun h => he.colorable ((H U V L R C lc).1 h),
    fun h => he.strict_density ((H U V L R C lc).2 h)⟩

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end

namespace SamplerParameters
open scoped BigOperators
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

def vertexEnumeration (p : SamplerParameters) {L R C : Type} [Fintype L] [Fintype R]
    [DecidableEq C] [DecidableEq (p.Vertices L R C)]
    (ec : ExplicitEnum C) (static : ExplicitEnum (p.Vertices L R Unit)) :
    ExplicitEnum (p.Vertices L R C) :=
  ExplicitEnum.ofCover ((ExplicitEnum.pi (ExplicitEnum.fin p.n) (fun _ => ec)).values.flatMap
    (fun chain => static.values.map (fun o => (chain,o.2)))) (by
      rintro ⟨chain,o⟩
      apply List.mem_flatMap.mpr
      refine ⟨chain,(ExplicitEnum.pi (ExplicitEnum.fin p.n) (fun _ => ec)).covers chain,?_⟩
      exact List.mem_map.mpr ⟨(fun _ => (),o),static.covers _,rfl⟩)

lemma vertexEnumeration_nonempty (p : SamplerParameters) {L R C : Type}
    [Fintype L] [Fintype R] [DecidableEq C] [DecidableEq (p.Vertices L R C)] [Nonempty C]
    (ec : ExplicitEnum C) (static : ExplicitEnum (p.Vertices L R Unit)) :
    0 < (p.vertexEnumeration ec static).values.length := by
  classical
  have h := (p.vertexEnumeration ec static).covers (Classical.choice (inferInstance : Nonempty (p.Vertices L R C)))
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem h)

lemma vertexEnumeration_length (p : SamplerParameters) {L R C : Type}
    [Fintype L] [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq (p.Vertices L R C)]
    (ec : ExplicitEnum C) (static : ExplicitEnum (p.Vertices L R Unit)) :
    (p.vertexEnumeration ec static).values.length ≤ Fintype.card C^p.n * static.values.length := by
  let xs := (ExplicitEnum.pi (ExplicitEnum.fin p.n) (fun _ => ec)).values
  have hh (xs : List (Fin p.n → C)) :
      (xs.flatMap (fun chain => static.values.map (fun o => (chain,o.2)))).length =
        xs.length * static.values.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_cons,ih]; ring
  change List.length (List.dedup _) ≤ _
  apply (List.dedup_sublist _).length_le.trans
  rw [hh]
  rw [ExplicitEnum.length_eq_card]
  simp only [Fintype.card_fun,Fintype.card_fin,le_refl]

attribute [instance] mixedTupleDecidableEq
attribute [instance 1100] mixedTupleComputableFintype

def namedOutput (p : SamplerParameters) (q : ℕ) (hq : 0<q)
    {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R] [DecidableEq C]
    [DecidableEq (p.Vertices L R C)] [Nonempty C]
    (lc : LabelCoverData U V L R C)
    (eu : ExplicitEnum U) (ev : ExplicitEnum V) (el : ExplicitEnum L) (er : ExplicitEnum R)
    (ec : ExplicitEnum C) (static : ExplicitEnum (p.Vertices L R Unit)) : Graph :=
  p.enumeratedOutput q hq lc (p.vertexEnumeration_nonempty ec static)
    (ExplicitEnum.grid eu ev el er p.n (p.m*2^p.k)).equiv
    (p.vertexEnumeration ec static).equiv

open scoped Classical
attribute [-instance] mixedTupleDecidableEq mixedTupleComputableFintype
noncomputable def namedOutput_renaming (p : SamplerParameters) (q : ℕ) (hq : 0<q)
    {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R] [DecidableEq C]
    [DecidableEq (p.Vertices L R C)] [Nonempty C]
    (lc : LabelCoverData U V L R C)
    (eu : ExplicitEnum U) (ev : ExplicitEnum V) (el : ExplicitEnum L) (er : ExplicitEnum R)
    (ec : ExplicitEnum C) (static : ExplicitEnum (p.Vertices L R Unit)) :
    Graph.Renaming (p.namedOutput q hq lc eu ev el er ec static) (p.output q hq lc) :=
  p.enumeratedOutput_renaming q hq lc _ _ _
attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

end SamplerParameters
end LargeIndependentSets

end OAI
