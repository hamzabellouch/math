import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy

namespace OAI

/-! # A literal finite list of all unit-exchange neighbors -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped Classical
open FactorialSignatures

variable {C : Type*} [DecidableEq C]

/-- The ordered pair records the coordinate raised and the coordinate lowered. -/
def exchangeTarget (X : C → ℕ) (i j : C) : C → ℕ := fun a =>
  X a+(if a=i then 1 else 0)-(if a=j then 1 else 0)

lemma adjacent_eq_exchangeTarget {X Y : C → ℕ} (h : IntegerExchangeAdjacent X Y) :
    ∃ i j,i≠j ∧ Y=exchangeTarget X i j := by
  obtain ⟨D,i,j,hij,hi,hj,rfl,rfl⟩ := h
  refine ⟨i,j,hij,?_⟩
  funext a
  unfold exchangeTarget removeOne
  by_cases hai : a=i
  · subst a
    simp only [hij,ite_true,ite_false,Nat.sub_zero]
    omega
  · by_cases haj : a=j
    · subst a
      simp only [hai,ite_true,ite_false,Nat.sub_zero,Nat.add_zero]
    · simp only [hai,haj,ite_false,Nat.sub_zero,Nat.add_zero]

noncomputable def exchangeCandidates [Fintype C] (X : C → ℕ) : Finset (C → ℕ) :=
  Finset.univ.image (fun p : C×C => exchangeTarget X p.1 p.2)

lemma adjacent_mem_candidates [Fintype C] {X Y : C → ℕ} (h : IntegerExchangeAdjacent X Y) :
    Y ∈ exchangeCandidates X := by
  obtain ⟨i,j,_,rfl⟩ := adjacent_eq_exchangeTarget h
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

theorem exchangeCandidates_card_le [Fintype C] (X : C → ℕ) :
    (exchangeCandidates X).card ≤ (Fintype.card C)^2 := by
  unfold exchangeCandidates
  exact (Finset.card_image_le).trans_eq (by simp only [Finset.card_univ,Fintype.card_prod,pow_two])

end ContingencyTables.IntegerWeightedTransport

end OAI
