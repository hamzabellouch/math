import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointPool
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafReplay
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteCross

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

def chosen (complete : ℚ  →  List (List X)) (T U : List (List X)) (b s : ℚ) : List (List X) :=
  if s=0 then T else if s=b then U else complete s

def count (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b s : ℚ) : ℕ :=
  ((after (insert (leaf s) Q) (chosen complete T U b s)) ∩ F).card

inductive Result (X : Type*) where
  | success (s : ℚ) (T : List (List X))
  | bracket (l u : ℚ) (T U : List (List X))

def range (f : ℚ  →  ℕ) (k N : ℕ) (b : ℚ) : ℚ × ℚ :=
  if f 0<k then
    let J := PriceBisection.search (fun s=>f (b-s)) k (PriceBisection.iterations 0 b N) (0,b)
    (b-J.2,b-J.1)
  else PriceBisection.search f k (PriceBisection.iterations 0 b N) (0,b)

lemma range_spec (f : ℚ  →  ℕ) (k N : ℕ) (b : ℚ) (hb : 0 ≤ b)
    (hs : Sandwich k (f 0) (f b)) :
    let J := range f k N b
    0 ≤ J.1  ∧  J.1 ≤ J.2  ∧  J.2 ≤ b  ∧  J.2-J.1 ≤ 1/(2:ℚ)^N  ∧
      (f J.1=k ∨ f J.2=k ∨ Sandwich k (f J.1) (f J.2)) := by
  dsimp only [range]
  split
  · rename_i hf
    have ha : k ≤ f b := by unfold Sandwich at hs; omega
    have hb' : f 0 ≤ k := hf.le
    obtain ⟨hl,hle,hu,hcl,hcu,hw⟩ := PriceBisection.search_spec (fun s=>f (b-s)) k
      (PriceBisection.iterations 0 b N) 0 b hb (by simpa using ha) (by simpa using hb')
    have hp := PriceBisection.iterations_precision 0 b N
    simp only [sub_zero] at hw hp
    refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
    unfold Sandwich
    dsimp only
    omega
  · rename_i hf
    have ha : k ≤ f 0 := by omega
    have hb' : f b ≤ k := by unfold Sandwich at hs; omega
    obtain ⟨hl,hle,hu,hcl,hcu,hw⟩ := PriceBisection.search_spec f k
      (PriceBisection.iterations 0 b N) 0 b hb ha hb'
    have hp := PriceBisection.iterations_precision 0 b N
    refine ⟨hl,hle,hu,hw ▸ hp,?_⟩
    unfold Sandwich
    omega

def run (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b : ℚ) (k N : ℕ) : Result X :=
  let f := count F Q leaf complete T U b
  let J := range f k N b
  if f J.1=k then .success J.1 (chosen complete T U b J.1)
  else if f J.2=k then .success J.2 (chosen complete T U b J.2)
  else .bracket J.1 J.2 (chosen complete T U b J.1) (chosen complete T U b J.2)

def Result.Spec (F Q : Finset X) (leaf : ℚ  →  X) (R : ℚ  →  List (List X)  →  Prop)
    (b : ℚ) (k N : ℕ) : Result X  →  Prop
  | .success s T => 0 ≤ s  ∧  s ≤ b  ∧  R s T  ∧  ((after (insert (leaf s) Q) T) ∩ F).card=k
  | .bracket l u T U => 0 ≤ l  ∧  l ≤ u  ∧  u ≤ b  ∧  u-l ≤ 1/(2:ℚ)^N  ∧  R l T  ∧  R u U  ∧
      Sandwich k ((after (insert (leaf l) Q) T) ∩ F).card ((after (insert (leaf u) Q) U) ∩ F).card

lemma run_spec (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b : ℚ) (k N : ℕ) (R : ℚ  →  List (List X)  →  Prop)
    (hb : 0<b) (hT : R 0 T) (hU : R b U) (hc : ∀ s,0 ≤ s → s ≤ b → R s (complete s))
    (hs : Sandwich k ((after (insert (leaf 0) Q) T) ∩ F).card ((after (insert (leaf b) Q) U) ∩ F).card) :
    (run F Q leaf complete T U b k N).Spec F Q leaf R b k N := by
  have hchoose : ∀ s,0 ≤ s → s ≤ b → R s (chosen complete T U b s) := by
    intro s hs0 hsb
    unfold chosen
    split_ifs with hz hu
    · subst s; exact hT
    · subst s; exact hU
    · exact hc s hs0 hsb
  have hs' : Sandwich k (count F Q leaf complete T U b 0) (count F Q leaf complete T U b b) := by
    simpa only [count,chosen,ite_true,ite_eq_right (ne_of_gt hb)] using hs
  obtain ⟨hl,hle,hu,hw,hcs⟩ := range_spec (count F Q leaf complete T U b) k N b hb.le hs'
  dsimp only [run]
  split
  · rename_i hk
    exact ⟨hl,hle.trans hu,hchoose _ hl (hle.trans hu),hk⟩
  · rename_i hk
    split
    · rename_i hk'
      exact ⟨hl.trans hle,hu,hchoose _ (hl.trans hle) hu,hk'⟩
    · rename_i hk'
      exact ⟨hl,hle,hu,hw,hchoose _ hl (hle.trans hu),hchoose _ (hl.trans hle) hu,
        (hcs.resolve_left hk).resolve_left hk'⟩

end MetricKMedianRecovery.CanonicalLengthSearch

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def EndpointSpec (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (v lam eta : ℝ) (q n k key : ℕ) (b : ℚ) (H : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V)) : Prop :=
  let C := J.common H
  let i := parent J.root
  Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta C ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
    (insert (leaf key i 0) (Q∪C.toFinset)) v lam (q+1) n (J.small T U) ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i b) B)
    (insert (leaf key i b) (Q∪C.toFinset)) v lam (q+1) n (J.large T U) ∧
  let a := ((after (insert (leaf key i 0) (Q∪C.toFinset)) (J.small T U))∩F.image original).card
  let c := ((after (insert (leaf key i b) (Q∪C.toFinset)) (J.large T U))∩F.image original).card
  a=k ∨ Sandwich k a c

lemma endpoints (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (B Q : Finset (Label V)) (v lam eta M : ℝ)
    (q n k key N : ℕ) (b : ℚ) (H G : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V))
    (hF : F.Nonempty) (hB : Before key B) (hQ : Q⊆F.image original∪B)
    (hdis : Disjoint (F.image original) B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hb : 20*N*M≤(b:ℝ))
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (hH : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H)
    (hG : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta G)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) B (Q∪G.toFinset) v lam (q+1) n U)
    (hacc : accepts (rows distance) (F.image original) H G J)
    (hs : Sandwich k (finalCount (F.image original) Q H T) (finalCount (F.image original) Q G U)) :
    EndpointSpec loc F B Q v lam eta q n k key b H T U J := by
  have hfar : ∀ (i : V) (C : List (Label V)) (W : List (List (Label V))),
      Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta C →
      Runs (fun j=>original (loc j)) (F.image original) B (Q∪C.toFinset) v lam (q+1) n W →
      Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i b) B)
        (insert (leaf key i b) (Q∪C.toFinset)) v lam (q+1) n W ∧
      finalCount (F.image original) Q C W=
        ((after (insert (leaf key i b) (Q∪C.toFinset)) W)∩F.image original).card := by
    intro i C W hC hW
    exact far_replay loc F B (Q∪C.toFinset) key i v lam M (q+1) n N b W
      hF hB hv hv1 hlam hM hN hlamUpper hb hdiam
      (PhaseHistoryTransfer.advance_rows _ _ _ _ _ _ _ _ C hv hv1 hlam hrow hC) hW
  cases J with
  | free i f =>
    obtain ⟨hi,hf,rfl,hco⟩ := hacc
    obtain ⟨i,hiV,rfl⟩ := Finset.mem_image.mp hi
    have hfB : f∈B := by
      have hh := hG.1.1.opened_subset (List.mem_toFinset.mpr (List.mem_append_right H (List.mem_cons_self ..)))
      exact (Finset.mem_union.mp hh).resolve_left hf
    have hdist : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f := by
      intro j
      rw [dist_comm (original (loc j)) (original i),dist_comm (original (loc j)) f]
      rw [← rows_spec loc distance hmetric,← rows_spec loc distance hmetric,hco j]
    obtain ⟨hz,hzcount⟩ := zero_free_replay loc F B Q key i f H U v lam eta q n hB hdis hQ hfB
      hdist (by linarith) hlam hG.1 hU
    obtain ⟨hb',hbcount⟩ := hfar i H T hH.1 hT
    refine ⟨hH,hz,hb',Or.inr ?_⟩
    simp only [Plan.root,Plan.common,Plan.small,Plan.large,parent,original,Function.Embedding.coeFn_mk,Sum.elim_inl,id_eq] at hzcount hbcount hs ⊢
    rw [←hzcount,←hbcount]
    exact hs.symm
  | paid C L i =>
    obtain ⟨hi,rfl,rfl⟩ := hacc
    obtain ⟨i,hiV,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hz,hzcount⟩ := zero_paid_replay loc F B Q key i C L T v lam eta q n hiV hB hdis hQ
      (by linarith) hlam hH.1 hT
    obtain ⟨hb',hbcount⟩ := hfar i (C++L) U hG.1 hU
    refine ⟨hG,hz,hb',?_⟩
    simp only [Plan.root,Plan.common,Plan.small,Plan.large,parent,original,Function.Embedding.coeFn_mk,Sum.elim_inl,id_eq] at hzcount hbcount hs ⊢
    rw [←hbcount]
    unfold Sandwich at hs ⊢
    omega

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
