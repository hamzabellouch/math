import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.CompleteGraph
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization

namespace OAI

namespace MatchingFPRAS
lemma vertex_bound_of_perfect {G : GraphInput} {M : Finset (Fin G.n×Fin G.n)}
    (hM : Perfect G M) : G.n≤2*G.edges.card := by
  classical
  have hc : (Finset.univ : Finset (Fin G.n))⊆M.image Prod.fst ∪ M.image Prod.snd := by
    intro v _
    obtain ⟨e,he,-⟩:=hM.2 v
    rcases he.2 with hv|hv
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he.1,hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he.1,hv⟩)
  have h₁:=Finset.card_le_card hc
  have h₂:=Finset.card_union_le (M.image Prod.fst) (M.image Prod.snd)
  have h₃:=Finset.card_image_le (s:=M) (f:=Prod.fst)
  have h₄:=Finset.card_image_le (s:=M) (f:=Prod.snd)
  have h₅:=Finset.card_le_card hM.1
  simp only [Finset.card_univ,Fintype.card_fin] at h₁
  omega

lemma zero_of_vertex_bound {G : GraphInput} (h : 2*G.edges.card<G.n) : Z G=0 := by
  classical
  by_contra hz
  obtain ⟨M,hM⟩:=Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hb:=vertex_bound_of_perfect ((mem_perfectMatchings G M).mp hM)
  omega

lemma even_of_perfect {G : GraphInput} {M : Finset (Fin G.n×Fin G.n)}
    (hM : Perfect G M) : Even G.n := by
  have h:=perfect_vertex_factor G M hM (fun _=>(-1:ℚ))
  have hh : (-1:ℚ)^G.n=1 := by
    simpa using h.symm
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1:ℚ)≠1)).mp hh

lemma zero_of_not_even {G : GraphInput} (he : ¬Even G.n) : Z G=0 := by
  by_contra hz
  obtain ⟨M,hM⟩:=Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  exact he (even_of_perfect ((mem_perfectMatchings G M).mp hM))

lemma count_empty_graph {G : GraphInput} (hn : G.n=0) : Z G=1 := by
  classical
  have hv (v : Fin G.n) : False := by have := v.isLt; omega
  have he : G.edges=∅ := Finset.eq_empty_of_forall_notMem (fun e _=>hv e.1)
  have hp : Perfect G ∅ := ⟨Finset.empty_subset _,fun v=>False.elim (hv v)⟩
  simp only [Z,perfectMatchings,he,Finset.powerset_empty]
  have hf : Finset.filter (Perfect G) {∅}=({∅} : Finset (Finset (Fin G.n×Fin G.n))) := by
    ext M
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl,hp⟩
  rw [hf]
  rfl

lemma edgeCard_le_input_length (G : GraphInput) (ε δ : ℚ) :
    G.edges.card≤(encodeInput G ε δ).length := by
  have hl (l : List (Fin G.n ×ₗ Fin G.n)) : l.length≤
      (l.flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val).length := by
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      have ha : 1≤(encodeNat (ofLex a).1.val).length := by
        simp only [encodeNat,List.length_append,List.length_map,List.length_singleton]
        omega
      omega
  have h:=hl ((G.edges.map toLex.toEmbedding).sort (·≤·))
  simp only [Finset.length_sort,Finset.card_map] at h
  simp only [encodeInput,List.length_append]
  omega

lemma positive_vertex_input_bound {G : GraphInput} (ε δ : ℚ) (hZ : 0<Z G) :
    G.n≤2*(encodeInput G ε δ).length := by
  obtain ⟨M,hM⟩:=Finset.card_pos.mp hZ
  exact (vertex_bound_of_perfect ((mem_perfectMatchings G M).mp hM)).trans
    (Nat.mul_le_mul_left 2 (edgeCard_le_input_length G ε δ))

namespace ExecutableInput
open TreeTyped TreeFunction

abbrev SparseInput := ℕ×List (ℕ×ℕ)
noncomputable def sparseRep (G : GraphInput) : SparseInput :=
  (G.n,(G.edges.toList.map (fun e=>(e.1.val,e.2.val))))
def tooSparse (x : SparseInput) : Bool := decide (2*x.2.length<x.1)
def tooSparseRealizer : Realizer tooSparse :=
  (composition (TreeTyped.pair (composition (TreeTyped.pair
    (composition second listLength) (composition second listLength)) add) first) less).congr (by
      intro x
      simp only [Function.comp_apply,tooSparse,two_mul])
lemma polynomial_tooSparse : PolynomialTime tooSparseRealizer := by
  unfold tooSparseRealizer
  apply polynomial_congr
  tree_cost

lemma tooSparse_source (G : GraphInput) : tooSparse (sparseRep G)=decide (2*G.edges.card<G.n) := by
  simp only [tooSparse,sparseRep,List.length_map,Finset.length_toList]
lemma tooSparse_zero (G : GraphInput) (h : tooSparse (sparseRep G)=true) : Z G=0 := by
  rw [tooSparse_source] at h
  exact zero_of_vertex_bound (of_decide_eq_true h)
lemma tooSparse_false_bound (G : GraphInput) (h : tooSparse (sparseRep G)=false) : G.n≤2*G.edges.card := by
  rw [tooSparse_source] at h
  have hh:=of_decide_eq_false h
  omega

lemma tooSparse_false_input_bound (G : GraphInput) (ε δ : ℚ)
    (h : tooSparse (sparseRep G)=false) : G.n≤2*(encodeInput G ε δ).length :=
  (tooSparse_false_bound G h).trans (Nat.mul_le_mul_left 2 (edgeCard_le_input_length G ε δ))

open TreePost Turing

theorem tooSparse_post : ∃ p : Polynomial ℕ,∀ x : SparseInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine tooSparseRealizer.program) (packed x) coins).state=none ∧
      (run (machine tooSparseRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (tooSparse x)) :=
  polynomial_compiles tooSparseRealizer polynomial_tooSparse
end ExecutableInput
end MatchingFPRAS

end OAI
