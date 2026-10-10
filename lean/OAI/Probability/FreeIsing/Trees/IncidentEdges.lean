import OAI.Probability.FreeIsing.Trees.Regularity

namespace OAI

noncomputable section
namespace Problem367

theorem card_incident_inducedEdges_le {d : ℕ} (D : Finset (TreeVertex d))
    (v : TreeVertex d) :
    ((inducedEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).card ≤ d := by
  classical
  let f : TreeVertex d × TreeVertex d → TreeVertex d :=
    fun e => if e.1 = v then e.2 else e.1
  have hdata {e : TreeVertex d × TreeVertex d}
      (he : e ∈ (inducedEdges D).filter (fun e => e.1 = v ∨ e.2 = v)) :
      (treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length) ∧
        (e.1 = v ∨ e.2 = v) := by
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_filter.mp he).2, hv⟩
  refine le_trans ?_ (Nat.le_of_eq (card_treeNeighborFinset v))
  apply Finset.card_le_card_of_injOn f
  · intro e he
    obtain ⟨⟨hadj, _⟩, hinc⟩ := hdata he
    change f e ∈ treeNeighborFinset v
    rw [mem_treeNeighborFinset]
    by_cases h : e.1 = v
    · simpa [f, h] using hadj
    · have h2 : e.2 = v := hinc.resolve_left h
      simpa [f, h, h2, treeAdj] using Or.symm hadj
  · rintro ⟨a, b⟩ he ⟨c, z⟩ he' h
    obtain ⟨⟨_, hab⟩, habv⟩ := hdata he
    obtain ⟨⟨_, hcz⟩, hczv⟩ := hdata he'
    change a.1.length < b.1.length at hab
    change c.1.length < z.1.length at hcz
    change a = v ∨ b = v at habv
    change c = v ∨ z = v at hczv
    by_cases ha : a = v
    · subst a
      by_cases hc : c = v
      · subst c
        have hbz : b = z := by simpa [f] using h
        exact Prod.ext rfl hbz
      · have hz : z = v := hczv.resolve_left hc
        subst z
        have hbc : b = c := by simpa [f, hc] using h
        subst c
        omega
    · have hb : b = v := habv.resolve_left ha
      subst b
      by_cases hc : c = v
      · subst c
        have haz : a = z := by simpa [f, ha] using h
        subst z
        omega
      · have hz : z = v := hczv.resolve_left hc
        subst z
        have hac : a = c := by simpa [f, ha, hc] using h
        exact Prod.ext hac rfl

end Problem367

end

end OAI
