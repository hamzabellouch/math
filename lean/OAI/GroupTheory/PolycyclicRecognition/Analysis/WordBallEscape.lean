import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordLength

namespace OAI

/-! # Every word ball in an infinite generated group has an outgoing edge -/
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G] [Infinite G]

theorem exists_wordBall_escape (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (n : ℕ) :
    ∃ y, y ∈ wordBall S (n + 1) ∧ y ∉ wordBall S n := by
  by_contra! h
  have hclosed (s : G) (hs : s ∈ S) (x : G) (hx : x ∈ wordBall S n) :
      s * x ∈ wordBall S n := by
    apply h
    have hs' : s ∈ wordBall S 1 :=
      (mem_wordBall_iff S 1 s).mpr ⟨[s], le_rfl, by simpa using hs, by simp⟩
    simpa only [Nat.add_comm 1 n] using mul_mem_wordBall hs' hx
  have hword (l : List G) (hl : ∀ s ∈ l, s ∈ S) : l.prod ∈ wordBall S n := by
    induction l with
    | nil => exact one_mem_wordBall S n
    | cons s l ih =>
      exact hclosed s (hl s (List.mem_cons_self ..)) l.prod
        (ih (fun t ht => hl t (List.mem_cons_of_mem s ht)))
  obtain ⟨z, hz⟩ := (wordBall S n).exists_notMem
  obtain ⟨m, hm⟩ := wordBall_exhaustive S hS hgen z
  obtain ⟨l, _, hl, rfl⟩ := (mem_wordBall_iff S m z).mp hm
  exact hz (hword l hl)

end PolycyclicRecognition

end OAI
