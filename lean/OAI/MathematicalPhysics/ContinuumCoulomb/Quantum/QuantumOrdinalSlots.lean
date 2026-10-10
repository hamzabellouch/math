import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridSlots

namespace OAI

/-! Explicit ordinal ranks give the required injective slots in each bounded
cell fiber. This is the finite ordering used by the spatial output program. -/

namespace ContinuumCoulomb.QuantumOrdinalSlots

def before {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => r < q ∧ cells r = cells q)

def rank {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) : ℕ := (before cells q).card

 theorem rank_lt_fiber {n : ℕ} (cells : Fin n → ℕ × ℕ) (q : Fin n) :
    rank cells q < (Finset.univ.filter (fun r => cells r = cells q)).card := by
  have hs : before cells q ⊆ Finset.univ.filter (fun r => cells r = cells q) := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.2⟩
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset hs).mpr
  refine ⟨q,by simp,?_⟩
  simp [before]

 theorem rank_lt {n : ℕ} (cells : Fin n → ℕ × ℕ) {q r : Fin n}
    (hqr : q < r) (hc : cells q = cells r) : rank cells q < rank cells r := by
  have hs : before cells q ⊆ before cells r := by
    intro a ha
    obtain ⟨_,hq,hcell⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq.trans hqr,hcell.trans hc⟩
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset hs).mpr
  refine ⟨q,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqr,hc⟩
  · simp [before]

 theorem rank_injective_on_cell {n : ℕ} (cells : Fin n → ℕ × ℕ) {q r : Fin n}
    (hc : cells q = cells r) (hr : rank cells q = rank cells r) : q=r := by
  rcases lt_trichotomy q r with h | h | h
  · have := rank_lt cells h hc
    omega
  · exact h
  · have := rank_lt cells h hc.symm
    omega

 def slot {n A : ℕ} (cells : Fin n → ℕ × ℕ)
    (hd : ∀ p, (Finset.univ.filter (fun q => cells q=p)).card ≤ A) (q : Fin n) : Fin A :=
  ⟨rank cells q,(rank_lt_fiber cells q).trans_le (hd (cells q))⟩

 theorem slot_injective_on_cell {n A : ℕ} (cells : Fin n → ℕ × ℕ)
    (hd : ∀ p, (Finset.univ.filter (fun q => cells q=p)).card ≤ A)
    {q r : Fin n} (hc : cells q = cells r) (hs : slot cells hd q = slot cells hd r) : q=r :=
  rank_injective_on_cell cells hc (congrArg Fin.val hs)

end ContinuumCoulomb.QuantumOrdinalSlots

end OAI
