import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSubdivision

namespace OAI

/-! Literal ordered site lists for each of the four subdivision terms.
The two finite subdivision stages reuse these lists, rather than selecting
a new support from an existential locality certificate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open scoped Classical

variable {ι κ : Type}

def appendMediator (xs : List ι) (e : κ) : List (ι ⊕ κ) :=
  xs.map Sum.inl ++ [Sum.inr e]

theorem appendMediator_nodup (xs : List ι) (hx : xs.Nodup) (e : κ) :
    (appendMediator xs e).Nodup := by
  apply (hx.map Sum.inl_injective).append (List.nodup_singleton _)
  intro x hx he
  have hxe : x = Sum.inr e := by simpa using he
  subst x
  simp at hx

theorem appendMediator_length (xs : List ι) (e : κ) :
    (appendMediator xs e).length = xs.length+1 := by
  simp [appendMediator]

def outputSites (xs : κ → List ι) (d : ℕ) (p : κ × Fin 4) : List (ι ⊕ κ) :=
  ![[],[Sum.inr p.1],appendMediator ((xs p.1).take d) p.1,
    appendMediator ((xs p.1).drop d) p.1] p.2

theorem outputSites_nodup (xs : κ → List ι) (d : ℕ)
    (hx : ∀ e, (xs e).Nodup) (p : κ × Fin 4) :
    (outputSites xs d p).Nodup := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact appendMediator_nodup _ ((hx e).sublist (List.take_sublist d _)) e
  · exact appendMediator_nodup _ ((hx e).sublist (List.drop_sublist d _)) e

theorem outputSites_length (xs : κ → List ι) (d : ℕ)
    (hx : ∀ e, (xs e).length ≤ 2*d) (p : κ × Fin 4) :
    (outputSites xs d p).length ≤ d+1 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change 0 ≤ d+1
    omega
  · change 1 ≤ d+1
    omega
  · change (appendMediator ((xs e).take d) e).length ≤ d+1
    rw [appendMediator_length,List.length_take]
    omega
  · change (appendMediator ((xs e).drop d) e).length ≤ d+1
    rw [appendMediator_length,List.length_drop]
    have := hx e
    omega

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem join_support_cover (xs : List ι) (a : ι → Fin 4)
    (ha : qmaPauliSupport a ⊆ xs.toFinset) (e : κ) (μ : Fin 4) :
    qmaPauliSupport (Sum.elim a (qmaSinglePauliWord e μ)) ⊆
      (appendMediator xs e).toFinset := by
  intro x hx
  cases x with
  | inl i =>
      have hi : i ∈ qmaPauliSupport a := by simpa [qmaPauliSupport] using hx
      have him := ha hi
      simpa [appendMediator] using him
  | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e μ) := by
        simpa [qmaPauliSupport] using hx
      have hje := qmaSinglePauliWord_support e μ hj
      have he : j = e := by simpa using hje
      simp [appendMediator,he]

theorem outputSites_cover (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs d w p) ⊆ (outputSites xs d p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,QuantumPolarizedSubdivision.word,qmaPauliSupport] at hx
    | inr j =>
        have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
          simpa [outputWord,QuantumPolarizedSubdivision.word,qmaPauliSupport] using hx
        have hje := qmaSinglePauliWord_support e 3 hj
        simpa [outputSites] using hje
  · exact join_support_cover ((xs e).take d)
      (QuantumOrderedSplit.firstWord (xs e) d (w e))
      (qmaPauliRestrict_support _ _) e _
  · exact join_support_cover ((xs e).drop d)
      (QuantumOrderedSplit.secondWord (xs e) d (w e))
      (qmaPauliRestrict_support _ _) e _

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
