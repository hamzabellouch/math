import Mathlib
import OAI.Combinatorics.ThinTrees.Flow.RootedFlow

namespace OAI

/-! Rooted relaxation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma parts_card {V : Type*} [Fintype V] (p : Setoid V) : (parts p).card=partCount p := by
  let f : Quotient p → parts p := Quotient.lift
    (fun v => ⟨block p v,block_mem_parts p v⟩)
    (fun a b h => Subtype.ext ((block_eq_iff p a b).mpr h))
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a,b using Quotient.inductionOn₂ with
      | h a b =>
        intro he
        exact Quotient.sound ((block_eq_iff p a b).mp (congrArg Subtype.val he))
    · intro A
      obtain ⟨v,hv⟩ := (mem_parts p A.val).mp A.property
      exact ⟨Quotient.mk p v,Subtype.ext hv⟩
  exact (Fintype.card_coe (parts p)).symm.trans (Fintype.card_congr (Equiv.ofBijective f hf)).symm

lemma parts_sum_card (p : Setoid (Fin n)) : ∑A ∈ parts p, A.card=n := by
  have h := card_biUnion (s:=parts p) (t:=id) 
    (fun A hA B hB hAB => parts_disjoint p hA hB hAB)
  have hcov : (parts p).biUnion id=(univ : Finset (Fin n)) := by
    ext v
    simp only [mem_biUnion,mem_univ,iff_true]
    exact ⟨block p v,block_mem_parts p v,self_mem_block p v⟩
  rw [hcov,card_univ,Fintype.card_fin] at h
  exact h.symm

lemma block_eq_of_part {p : Setoid (Fin n)} {S : Finset (Fin n)}
    (hS : S ∈ parts p) {v : Fin n} (hv : v ∈ S) : S=block p v := by
  obtain ⟨w,rfl⟩ := (mem_parts p S).mp hS
  exact (block_eq_iff p w v).mpr ((mem_block p w v).mp hv)

lemma internal_partition_accounting (G : MultiGraph n m) (x : Fin m → ℝ)
    (p : Setoid (Fin n)) :
    (∑S ∈ parts p, ∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e)+
      capacity G.left G.right x p = ∑e, x e := by
  simp only [sum_filter,capacity]
  rw [sum_comm,←sum_add_distrib]
  apply sum_congr rfl
  intro e he
  have hi : (∑S ∈ parts p, if G.left e ∈ S ∧ G.right e ∈ S then x e else 0)=
      if p (G.left e) (G.right e) then x e else 0 := by
    rw [sum_eq_single (block p (G.left e))]
    · simp only [self_mem_block,mem_block,true_and]
    · intro S hS hSne
      apply ite_eq_right
      rintro ⟨hl,hr⟩
      exact hSne (block_eq_of_part hS hl)
    · intro h
      exact (h (block_mem_parts p (G.left e))).elim
  rw [hi,crossingIndicator]
  split_ifs <;> ring

structure FlowPoint (n m : ℕ) where
  x : Fin m → ℝ
  a : Fin n → Fin m → ℝ
  b : Fin n → Fin m → ℝ

def FlowPoint.Feasible (G : MultiGraph n m) (c : Fin m → ℝ) (qbar ε : ℝ)
    (F : FlowPoint n m) : Prop :=
  (∀e, 0 ≤ F.x e ∧ F.x e ≤ c e) ∧
  (∀r e, 0 ≤ F.a r e ∧ 0 ≤ F.b r e ∧ F.x e ≤ F.a r e+F.b r e) ∧
  (∀r v, out G (F.a r) (F.b r) v ≤ if v=r then ε else qbar) ∧
  qbar*((n:ℝ)-1)-ε ≤ ∑e, F.x e

lemma sum_root_budget {S : Finset (Fin n)} {r : Fin n} (hr : r ∈ S) (qbar ε : ℝ) :
    (∑v ∈ S, if v=r then ε else qbar) = qbar*((S.card:ℝ)-1)+ε := by
  have he (v : Fin n) : (if v=r then ε else qbar) =
      (if v=r then ε-qbar else 0)+qbar := by split_ifs <;> ring
  simp only [he,sum_add_distrib,sum_ite_eq',hr,ite_true,sum_const,nsmul_eq_mul]
  ring

lemma internal_flow_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), F.x e) ≤
      qbar*((S.card:ℝ)-1)+ε := by
  obtain ⟨r,hr⟩ := hS
  calc
    _ ≤ ∑v ∈ S, out G (F.a r) (F.b r) v :=
      internal_le_out G (fun e => (hF.2.1 r e).1) (fun e => (hF.2.1 r e).2.1)
        (fun e => (hF.2.1 r e).2.2) S
    _ ≤ ∑v ∈ S, if v=r then ε else qbar := sum_le_sum fun v _ => hF.2.2.1 r v
    _ = _ := sum_root_budget hr qbar ε

lemma flow_partition_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε) (p : Setoid (Fin n)) :
    qbar*((partCount p:ℝ)-1)-ε*((partCount p:ℝ)+1) ≤ capacity G.left G.right c p := by
  have hi := sum_le_sum (s:=parts p) (fun S hS => internal_flow_bound G c hF S
    ((parts_partition p).1 S hS).1)
  have hs : (∑S ∈ parts p, (qbar*((S.card:ℝ)-1)+ε))=
      qbar*((n:ℝ)-partCount p)+ε*partCount p := by
    simp only [mul_sub,mul_one,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    rw [←Nat.cast_sum,parts_sum_card,parts_card]
    ring
  rw [hs] at hi
  have hcross : capacity G.left G.right F.x p ≤ capacity G.left G.right c p :=
    sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hF.1 e).2 (crossingIndicator_nonneg _ _ _)
  have htotal := hF.2.2.2
  have haccount := internal_partition_accounting G F.x p
  linarith

theorem relaxed_flow_implies_partitions (G : MultiGraph n m) (hn : 0 < n)
    (c : Fin m → ℝ) {q ε : ℝ} (hε : 0 ≤ ε) {F : FlowPoint n m}
    (hF : F.Feasible G c (q+4*ε) ε) :
    ∀p, 0 ≤ slack G.left G.right c q p := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  intro p
  by_cases hp : p=⊤
  · subst p
    simp [slack,capacity,crossingIndicator,partCount_top]
  · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount hp
    have hb := flow_partition_bound G c hF p
    have he : 0 ≤ ε*(3*(partCount p:ℝ)-5) := mul_nonneg hε (by linarith)
    dsimp [slack]
    nlinarith only [hb,he]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
