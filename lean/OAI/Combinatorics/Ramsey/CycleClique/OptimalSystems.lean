import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

def PathSystem.Optimal {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (k : ℕ) (P : PathSystem G Q) : Prop :=
  P.amount < k + 1 - Q.ncard ∧
  (∀ R : PathSystem G Q, R.amount < k + 1 - Q.ncard → R.amount ≤ P.amount) ∧
  (∀ R : PathSystem G Q, R.amount = P.amount → P.edgeCount ≤ R.edgeCount)

theorem PathSystem.exists_optimal {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) {k : ℕ} (ht : Q.ncard ≤ k) :
    ∃ P : PathSystem G Q, P.Optimal k := by
  classical
  let T : ℕ → Prop := fun a => ∃ P : PathSystem G Q, P.amount = a
  let L := Nat.findGreatest T (k - Q.ncard)
  have hT0 : T 0 := ⟨PathSystem.empty G Q, PathSystem.empty_amount G Q⟩
  have hTL : T L := Nat.findGreatest_spec (Nat.zero_le _) hT0
  let E : ℕ → Prop := fun e => ∃ P : PathSystem G Q, P.amount = L ∧ P.edgeCount = e
  have hE : ∃ e, E e := by obtain ⟨P, hP⟩ := hTL; exact ⟨P.edgeCount, P, hP, rfl⟩
  obtain ⟨P, hPL, hPe⟩ := Nat.find_spec hE
  refine ⟨P, ?_, ?_, ?_⟩
  · have hh := Nat.findGreatest_le (P := T) (k - Q.ncard)
    dsimp [L] at hPL
    omega
  · intro R hR
    have hh := Nat.le_findGreatest (P := T) (show R.amount ≤ k - Q.ncard by omega)
      ⟨R, rfl⟩
    dsimp [L] at hPL
    omega
  · intro R hR
    have hh := Nat.find_min' hE (show E R.edgeCount from ⟨R, hR.trans hPL, rfl⟩)
    omega

 

theorem PathSystem.optimality {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    (R : PathSystem G Q)
    (hl : P.amount ≤ R.amount) (htie : P.amount = R.amount → R.edgeCount < P.edgeCount)
    (hu : R.amount ≤ k + 1 - R.incident) : False := by
  by_cases hh : k + 1 - Q.ncard ≤ R.amount
  · exact R.closing_interval hk hQ hcycle ht hh hu
  · have hle := hopt.2.1 R (by omega)
    have heq : R.amount = P.amount := by omega
    have he := hopt.2.2 R heq
    have he' := htie heq.symm
    omega

 
theorem isChain_bridge {V : Type*} {R : V → V → Prop}
    (hR : ∀ ⦃first second⦄, R first second → R second first)
    {x y : V} {u v I : List V} (hu : (x :: u).IsChain R)
    (hv : (y :: v).IsChain R) (hI : (x :: I ++ [y]).IsChain R) :
    ((x :: u).reverse ++ I ++ (y :: v)).IsChain R := by
  have hr : (u.reverse ++ [x]).IsChain R := by
    simpa using List.isChain_reverse.mpr (hu.imp (fun _ _ h => hR h))
  have h₁ : (u.reverse ++ [x] ++ (I ++ [y])).IsChain R :=
    hr.append_overlap hI (by simp)
  have h₂ : ((u.reverse ++ [x] ++ I) ++ [y] ++ v).IsChain R := by
    apply List.IsChain.append_overlap (l₂ := [y]) (by simpa only [List.append_assoc] using h₁)
      (by simpa using hv) (by simp)
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h₂

theorem nodup_bridge {V : Type*} {A B C I : List V}
    (h : (A ++ B ++ C).Nodup) (hi : I.Nodup) (hdis : I.Disjoint (A ++ B ++ C)) :
    (A.reverse ++ I ++ B ++ C).Nodup := by
  have hsym := hdis.symm
  simp only [List.nodup_append, List.nodup_reverse, List.mem_append, List.mem_reverse,
    List.disjoint_left] at *
  aesop

 

theorem PathSystem.join_tails {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    (C : List (List V)) {x y : V} (u v I : List V)
    (hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten)
    (hne : ∀ c ∈ C, c ≠ []) (hc : ∀ c ∈ C, c.IsChain G.Adj)
    (hcp : ∀ c ∈ C, c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hce : ∀ c ∈ C, (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q))
    (hu : (x :: u).IsChain G.Adj) (hv : (y :: v).IsChain G.Adj)
    (hup : (x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hvp : (y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hue : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.chains.length = C.length + 1 := by
  classical
  let J := (x :: u).reverse ++ I ++ (y :: v)
  have hJn : J ≠ [] := by simp [J]
  have hnd : (J ++ C.flatten).Nodup := by
    apply nodup_bridge (hperm.nodup_iff.mpr P.nodup) hIn
    apply List.disjoint_left.mpr
    intro a ha hb
    exact List.disjoint_left.mp hId ha (hperm.subset hb)
  have hJe : (∀ a ∈ J.head?, a ∈ Q) ∧ (∀ a ∈ J.getLast?, a ∈ Q) := by
    constructor
    · intro a ha
      apply hue a
      simpa only [J, List.append_assoc, List.head?_append_of_ne_nil _ (by simp : (x :: u).reverse ≠ []),
        List.head?_reverse] using ha
    · intro a ha
      apply hve a
      simpa only [J, ← List.append_assoc,
        List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using ha
  let R : PathSystem G Q :=
    { chains := J :: C
      nonempty := by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
      nodup := hnd
      edges := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
        · exact hc c hc'
      positive := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
        · exact hcp c hc'
      ends := by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
      cover := by
        intro a ha
        have hh := hperm.mem_iff.mpr (P.cover a ha)
        simp only [J, List.flatten_cons, List.mem_append, List.mem_reverse] at hh ⊢
        tauto }
  refine ⟨R, ?_, rfl⟩
  have hh := hperm.length_eq
  rw [P.flat_length] at hh
  change ((x :: u).reverse ++ I ++ (y :: v) ++ C.flatten).length - Q.ncard =
    P.amount + I.length
  simp only [List.length_append, List.length_reverse] at hh ⊢
  omega

end CycleClique

end OAI
