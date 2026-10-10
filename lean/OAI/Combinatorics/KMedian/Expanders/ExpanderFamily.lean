import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SmallBias
import OAI.Combinatorics.KMedian.Expanders.Zigzag
import OAI.Combinatorics.KMedian.Expanders.GraphRelabel

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

abbrev SmallPort := Fin (2^44)
abbrev Degree := SmallPort × SmallPort
abbrev Branch := Degree × Degree

def growth : ℕ := (2^44)^4

lemma growth_gt_one : 1 < growth := by norm_num [growth]

noncomputable def baseVertexEquiv : BitVector (Fin 176) ≃ Branch :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Fintype.card_prod]
    norm_num)

noncomputable def base : PortGraph Branch SmallPort :=
  Walsh.baseGraph.relabel baseVertexEquiv (Equiv.refl SmallPort)

lemma base_contracts : base.Contracts (1/10) :=
  Walsh.baseGraph.relabel_contracts baseVertexEquiv (Equiv.refl SmallPort) Walsh.baseGraph_contracts

def Vertex : ℕ → Type
  | 0 => Unit
  | n+1 => Vertex n × Branch

instance vertexFintype : (n : ℕ) → Fintype (Vertex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := vertexFintype n; inferInstanceAs (Fintype (Vertex n × Branch))

instance vertexNonempty : (n : ℕ) → Nonempty (Vertex n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => letI := vertexNonempty n; inferInstanceAs (Nonempty (Vertex n × Branch))

noncomputable def graph : (n : ℕ) → PortGraph (Vertex n) Degree
  | 0 => { rotate := Equiv.refl _
           involutive := fun _ => rfl }
  | n+1 => (graph n).square.zigzag base

lemma graph_contracts : ∀ n, (graph n).Contracts (1/2) := by
  intro n
  induction n with
  | zero =>
    let : Subsingleton (Vertex 0) := inferInstanceAs (Subsingleton Unit)
    intro f hf
    have he : f=fun _ => 0 := by
      funext v
      have hc : (𝔼 w, f w)=f v := by
        have hh : f=fun _ => f v := funext (fun w => congrArg f (Subsingleton.elim w v))
        rw [hh,Fintype.expect_const]
      exact hc.symm.trans hf
    rw [he,PortGraph.adjacency_const]
    simp [energy]
  | succ n ih => exact PortGraph.square_zigzag_half (graph n) base ih base_contracts

lemma card_branch : Fintype.card Branch=growth := by
  simp only [Fintype.card_prod,Fintype.card_fin,growth]
  ring

lemma card_vertex (n : ℕ) : Fintype.card (Vertex n)=growth^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × Branch)=growth^(n+1)
    rw [Fintype.card_prod,ih,card_branch,pow_succ]

def level (n : ℕ) : ℕ := Nat.log growth (n+1)+1

lemma padding_lower (n : ℕ) : n+1 ≤ Fintype.card (Vertex (level n)) := by
  rw [card_vertex]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self growth_gt_one (n+1))

lemma padding_upper (n : ℕ) : Fintype.card (Vertex (level n)) ≤ growth*(n+1) := by
  rw [card_vertex,level,pow_succ]
  have h := Nat.pow_log_le_self growth (Nat.succ_ne_zero n)
  exact (Nat.mul_le_mul_right growth h).trans_eq (Nat.mul_comm _ _)

lemma recursive_calls_le_size (n : ℕ) : 2^n ≤ Fintype.card (Vertex n) := by
  rw [card_vertex]
  exact Nat.pow_le_pow_left (by have := growth_gt_one; omega) n

lemma padded_recursive_calls (n : ℕ) : 2^(level n) ≤ growth*(n+1) :=
  (recursive_calls_le_size (level n)).trans (padding_upper n)

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
