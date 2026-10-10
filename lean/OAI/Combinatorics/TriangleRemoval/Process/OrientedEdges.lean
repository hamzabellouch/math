import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddings
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def orientedEdges {n : ℕ} (G : Graph n) : Finset (Fin n × Fin n) :=
  G.biUnion (fun e => (e ×ˢ e).filter (fun z => z.1 ≠ z.2))

@[simp] lemma mem_orientedEdges {n : ℕ} {G : Graph n}
    (hG : ∀ e ∈ G, e.card = 2) (x y : Fin n) :
    (x,y) ∈ orientedEdges G ↔ (lookupGraph G).Adj x y := by
  simp only [orientedEdges,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨e,he,⟨hx,hy⟩,hxy⟩
    refine ⟨hxy,?_⟩
    have heq : ({x,y} : Finset (Fin n)) = e :=
      Finset.eq_of_subset_of_card_le (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy)
        (by rw [hG e he,Finset.card_pair hxy])
    exact heq.symm ▸ he
  · rintro ⟨hxy,he⟩
    exact ⟨{x,y},he,⟨by simp,by simp⟩,hxy⟩

theorem orientedEdges_card_le {n : ℕ} {G : Graph n} (hG : ∀ e ∈ G, e.card = 2) :
    (orientedEdges G).card ≤ 2 * G.card := by
  unfold orientedEdges
  calc
    _ ≤ ∑ e ∈ G, ((e ×ˢ e).filter (fun z => z.1 ≠ z.2)).card := Finset.card_biUnion_le
    _ = ∑ _e ∈ G, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (hG e he)
      have hh : (({x,y} : Finset (Fin n)) ×ˢ {x,y}).filter (fun z => z.1 ≠ z.2) =
          {(x,y),(y,x)} := by
        ext z
        rcases z with ⟨u,v⟩
        simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_insert,
          Finset.mem_singleton,Prod.mk.injEq]
        aesop
      rw [hh,Finset.card_pair]
      exact fun h => hxy (congrArg Prod.fst h)
    _ = _ := by simp [mul_comm]

open Classical in

theorem prefixEmbeddings_root_cover {n N R r : ℕ} (J : SimpleGraph (Fin N))
    (G : Graph n) (hG : ∀ e ∈ G, e.card = 2) (hR : R ≤ N)
    (u v : Fin r → Fin R)
    (hcover : ∀ i : Fin R, ∃ j, i = u j ∨ i = v j)
    (hedge : ∀ j, J.Adj (Fin.castLE hR (u j)) (Fin.castLE hR (v j))) :
    (prefixEmbeddings J (lookupGraph G) R hR).card ≤ (2 * G.card)^r := by
  classical
  let s := prefixEmbeddings J (lookupGraph G) R hR
  let f : s → (Fin r → ↥(orientedEdges G)) := fun φ j =>
    ⟨(φ.val (u j),φ.val (v j)),(mem_orientedEdges hG _ _).mpr
      ((mem_prefixEmbeddings φ.val).mp φ.property _ _ (hedge j))⟩
  have hi : Function.Injective f := by
    intro φ ψ he
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    obtain ⟨j,hi | hi⟩ := hcover i
    · subst i
      exact congrArg (fun z : ↥(orientedEdges G) => z.val.1) (congrFun he j)
    · subst i
      exact congrArg (fun z : ↥(orientedEdges G) => z.val.2) (congrFun he j)
  have hc := Fintype.card_le_of_injective f hi
  simp only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] at hc
  exact hc.trans (Nat.pow_le_pow_left (orientedEdges_card_le hG) r)

end SharpTerminalLeave

end

end OAI
