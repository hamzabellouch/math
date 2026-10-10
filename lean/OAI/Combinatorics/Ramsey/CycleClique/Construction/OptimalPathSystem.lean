import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathSystem

namespace OAI

/-! Existence and the exact optimality criterion for manuscript Section 6. -/

namespace CycleClique.Construction.ExpandedPathSystem

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

/-- Maximize the total amount below `k+1-|Q|`, then minimize the number of
assigned paths. Both optimization orders are on natural numbers. -/
structure IsOptimal (S : ExpandedPathSystem G Q) (k : ℕ) : Prop where
  budget : S.amount ≤ k - Q.card
  maximal : ∀ T : ExpandedPathSystem G Q, T.amount ≤ k - Q.card → T.amount ≤ S.amount
  minimal : ∀ T : ExpandedPathSystem G Q, T.amount = S.amount →
    S.assignedCount ≤ T.assignedCount

/-- The empty system ensures existence, even when the amount budget is zero. -/
theorem exists_optimal (G : SimpleGraph V) (Q : Finset V) (k : ℕ) :
    ∃ S : ExpandedPathSystem G Q, S.IsOptimal k := by
  classical
  let b := k - Q.card
  have hex : ∃ d, ∃ T : ExpandedPathSystem G Q, T.amount + d = b := by
    exact ⟨b, empty G Q, by simp⟩
  obtain ⟨S₀, hS₀⟩ := Nat.find_spec hex
  have hmax : ∀ T : ExpandedPathSystem G Q, T.amount ≤ b → T.amount ≤ S₀.amount := by
    intro T hT
    have hd := Nat.find_min' hex (show ∃ S : ExpandedPathSystem G Q,
      S.amount + (b - T.amount) = b from ⟨T, Nat.add_sub_of_le hT⟩)
    omega
  have he : ∃ e, ∃ T : ExpandedPathSystem G Q,
      T.amount = S₀.amount ∧ T.assignedCount = e := ⟨S₀.assignedCount, S₀, rfl, rfl⟩
  obtain ⟨S, hSamount, hSe⟩ := Nat.find_spec he
  refine ⟨S, ⟨?_, ?_, ?_⟩⟩
  · change S.amount ≤ b
    omega
  · intro T hT
    rw [hSamount]
    exact hmax T hT
  · intro T hT
    rw [hSe]
    exact Nat.find_min' he ⟨T, hT.trans hSamount, rfl⟩

theorem incident_le (S : ExpandedPathSystem G Q) : S.incident ≤ Q.card := by
  classical
  exact Finset.card_le_card Finset.inter_subset_right

/-- Manuscript Lemma `path:optimality`, retaining its exact indicator and
the secondary minimization of the number of assigned paths. -/
theorem IsOptimal.criterion {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (T : ExpandedPathSystem G Q)
    (hlow : S.amount + (if S.assignedCount ≤ T.assignedCount then 1 else 0) ≤ T.amount)
    (hhigh : T.amount + T.incident ≤ k + 1) : False := by
  by_cases hthreshold : k + 1 - Q.card ≤ T.amount
  · exact T.forbidden_interval hk hQ hcycle hthreshold hhigh
  have hTbudget : T.amount ≤ k - Q.card := by omega
  have hmax := hopt.maximal T hTbudget
  by_cases he : S.assignedCount ≤ T.assignedCount
  · simp only [he, ↓reduceIte] at hlow
    omega
  · simp only [he, ↓reduceIte, Nat.add_zero] at hlow
    have hamount : T.amount = S.amount := by omega
    exact he (hopt.minimal T hamount)

/-- A valid improvement by one outside vertex is impossible, regardless
of how the number of represented paths changes. -/
theorem IsOptimal.no_one_vertex_increase {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (T : ExpandedPathSystem G Q) (hinc : T.amount = S.amount + 1) : False := by
  apply hopt.criterion hk hQk hQ hcycle T
  · split_ifs <;> omega
  · have hb := hopt.budget
    have hi := T.incident_le
    omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
