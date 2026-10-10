import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma graphCandidate_iff {n : ℕ} (G : Graph n) (focus : Graph n)
    (parent : Option (Finset (Fin n))) (p : Finset (Fin n) × Finset (Fin n)) :
    p ∈ gridCandidates (triangleHypergraph G) focus parent ↔
      p.1 ∈ focus ∧ p.2 ∈ triangles G ∧ p.1 ∈ p.2.powersetCard 2 ∧ some p.2 ≠ parent := by
  rcases p with ⟨e,T⟩
  simp only [gridCandidates,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,and_true]
  by_cases ht : T ∈ triangles G
  · simp only [triangleHypergraph,ht,↓reduceIte,true_and]
  · simp only [triangleHypergraph,ht,↓reduceIte,Finset.notMem_empty,false_and,and_false]

lemma triangle_third_exists {α : Type*} [DecidableEq α] {T e : Finset α}
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) :
    ∃ x, x ∉ e ∧ T = insert x e := by
  obtain ⟨heT,hce⟩ := Finset.mem_powersetCard.mp he
  have hdiff : (T \ e).card = 1 := by
    rw [Finset.card_sdiff,Finset.inter_eq_left.mpr heT,hT,hce]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hdiff
  have hxm : x ∈ T \ e := by rw [hx]; simp
  refine ⟨x,(Finset.mem_sdiff.mp hxm).2,?_⟩
  have hh := Finset.sdiff_union_of_subset heT
  rw [hx,Finset.singleton_union] at hh
  exact hh.symm

noncomputable def triangleThird {α : Type*} [DecidableEq α] (T e : Finset α)
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) : α :=
  (triangle_third_exists hT he).choose

lemma triangleThird_spec {α : Type*} [DecidableEq α] (T e : Finset α)
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) :
    triangleThird T e hT he ∉ e ∧ T = insert (triangleThird T e hT he) e :=
  (triangle_third_exists hT he).choose_spec

namespace RecordedCallForest
section Incoming
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
variable {H : τ → Finset ι} {c : QueryCall ι τ} (F : RecordedCallForest H c)

noncomputable def incoming (i : Fin F.size) (hi : i ≠ F.root) : ι × τ :=
  (F.is_child i hi).choose

theorem incoming_spec (i : Fin F.size) (hi : i ≠ F.root) :
    F.incoming i hi ∈ gridCandidates H (F.call (F.parent i hi)).focus
      (F.call (F.parent i hi)).parent ∧
    F.call i = ⟨F.incoming i hi :: (F.call (F.parent i hi)).address,
      (H (F.incoming i hi).2).erase (F.incoming i hi).1,some (F.incoming i hi).2⟩ :=
  (F.is_child i hi).choose_spec

theorem incoming_unique (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (hp : F.parent i hi = F.parent j hj) (he : F.incoming i hi = F.incoming j hj) : i = j := by
  apply F.address_injective
  change (F.call i).address = (F.call j).address
  rw [(F.incoming_spec i hi).2,(F.incoming_spec j hj).2]
  simp only [hp,he]

end Incoming

section GraphIncoming
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma incoming_graph (i : Fin F.size) (hi : i ≠ F.root) :
    (F.incoming i hi).1 ∈ (F.call (F.parent i hi)).focus ∧
    (F.incoming i hi).2 ∈ triangles G ∧
    (F.incoming i hi).1 ∈ (F.incoming i hi).2.powersetCard 2 ∧
    some (F.incoming i hi).2 ≠ (F.call (F.parent i hi)).parent :=
  (graphCandidate_iff G _ _ _).mp (F.incoming_spec i hi).1

noncomputable def newVertex (i : Fin F.size) (hi : i ≠ F.root) : Fin n :=
  triangleThird (F.incoming i hi).2 (F.incoming i hi).1
    (mem_triangles.mp (F.incoming_graph i hi).2.1).1 (F.incoming_graph i hi).2.2.1

lemma newVertex_spec (i : Fin F.size) (hi : i ≠ F.root) :
    F.newVertex i hi ∉ (F.incoming i hi).1 ∧
    (F.incoming i hi).2 = insert (F.newVertex i hi) (F.incoming i hi).1 :=
  triangleThird_spec _ _ _ _

lemma incoming_card (i : Fin F.size) (hi : i ≠ F.root) :
    (F.incoming i hi).1.card = 2 :=
  (Finset.mem_powersetCard.mp (F.incoming_graph i hi).2.2.1).2

lemma incoming_parent (i : Fin F.size) (hi : i ≠ F.root) :
    (F.call i).parent = some (F.incoming i hi).2 := by
  rw [(F.incoming_spec i hi).2]

lemma incoming_focus (i : Fin F.size) (hi : i ≠ F.root) :
    (F.call i).focus = ((F.incoming i hi).2.powersetCard 2).erase (F.incoming i hi).1 := by
  rw [(F.incoming_spec i hi).2]
  simp only [triangleHypergraph,(F.incoming_graph i hi).2.1,↓reduceIte]

lemma incoming_of_nonroot_parent (i : Fin F.size) (hi : i ≠ F.root)
    (hp : F.parent i hi ≠ F.root) :
    (F.incoming i hi).1 ⊆ insert (F.newVertex (F.parent i hi) hp)
      (F.incoming (F.parent i hi) hp).1 ∧
    (F.incoming i hi).1 ≠ (F.incoming (F.parent i hi) hp).1 ∧
    (F.incoming i hi).2 ≠ (F.incoming (F.parent i hi) hp).2 := by
  have hc := F.incoming_graph i hi
  rw [F.incoming_focus _ hp] at hc
  obtain ⟨hediff,hepow⟩ := Finset.mem_erase.mp hc.1
  refine ⟨?_,hediff,?_⟩
  · rw [← (F.newVertex_spec _ hp).2]
    exact (Finset.mem_powersetCard.mp hepow).1
  · rw [F.incoming_parent _ hp] at hc
    exact fun he => hc.2.2.2 (congrArg some he)

end GraphIncoming
end RecordedCallForest
end SharpTerminalLeave

end

end OAI
