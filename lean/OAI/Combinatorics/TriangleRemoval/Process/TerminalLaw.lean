import Mathlib
import OAI.Combinatorics.TriangleRemoval.Model

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

@[simp] theorem card_completeGraph (n : ℕ) : (completeGraph n).card = n.choose 2 := by
  simp [completeGraph, Finset.card_powersetCard]

@[simp] theorem mem_completeGraph {n : ℕ} {e : Finset (Fin n)} :
    e ∈ completeGraph n ↔ e.card = 2 := by
  simp [completeGraph, Finset.mem_powersetCard]

@[simp] theorem mem_triangles {n : ℕ} {G : Graph n} {t : Finset (Fin n)} :
    t ∈ triangles G ↔ t.card = 3 ∧ t.powersetCard 2 ⊆ G := by
  simp [triangles, Finset.mem_powersetCard]

theorem triangles_mono {n : ℕ} {G H : Graph n} (h : H ⊆ G) :
    triangles H ⊆ triangles G := by
  intro t ht
  obtain ⟨hc, he⟩ := mem_triangles.mp ht
  exact mem_triangles.mpr ⟨hc, he.trans h⟩

theorem triangle_edge_card {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) : (t.powersetCard 2).card = 3 := by
  rw [Finset.card_powersetCard, (mem_triangles.mp ht).1]
  decide

theorem three_le_card_of_triangle {n : ℕ} {G : Graph n}
    (h : (triangles G).Nonempty) : 3 ≤ G.card := by
  obtain ⟨t, ht⟩ := h
  have hc := Finset.card_le_card (mem_triangles.mp ht).2
  rwa [triangle_edge_card ht] at hc

theorem step_support_active {n : ℕ} {G H : Graph n}
    (h : (triangles G).Nonempty) :
    H ∈ (step G).support ↔ ∃ t ∈ triangles G, G \ t.powersetCard 2 = H := by
  simp only [step, dite_eq_left h, PMF.mem_support_map_iff,
    PMF.mem_support_uniformOfFinset_iff]

theorem step_absorbing {n : ℕ} {G : Graph n} (h : triangles G = ∅) :
    step G = PMF.pure G := by
  simp [step, h]

theorem step_support_subset {n : ℕ} {G H : Graph n} (h : H ∈ (step G).support) :
    H ⊆ G := by
  by_cases hG : (triangles G).Nonempty
  · obtain ⟨t, _, rfl⟩ := (step_support_active hG).mp h
    exact Finset.sdiff_subset
  · simp only [step, dite_eq_right hG, PMF.mem_support_pure_iff] at h
    exact h ▸ Finset.Subset.refl G

theorem step_card_of_active {n : ℕ} {G H : Graph n}
    (hG : (triangles G).Nonempty) (h : H ∈ (step G).support) :
    H.card + 3 = G.card := by
  obtain ⟨t, ht, rfl⟩ := (step_support_active hG).mp h
  have hc := Finset.card_sdiff_add_card_eq_card (mem_triangles.mp ht).2
  rwa [triangle_edge_card ht] at hc

theorem evolve_support_subset {n : ℕ} (G : Graph n) (k : ℕ) {H : Graph n}
    (h : H ∈ (evolve G k).support) : H ⊆ G := by
  induction k generalizing H with
  | zero =>
    simp only [evolve, PMF.mem_support_pure_iff] at h
    exact h ▸ Finset.Subset.refl G
  | succ k ih =>
    obtain ⟨J, hJ, hH⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    exact (step_support_subset hH).trans (ih hJ)

theorem evolve_card_of_active {n : ℕ} (G : Graph n) (k : ℕ) {H : Graph n}
    (h : H ∈ (evolve G k).support) (hH : (triangles H).Nonempty) :
    H.card + 3 * k = G.card := by
  induction k generalizing H with
  | zero =>
    simp only [evolve, PMF.mem_support_pure_iff] at h
    simp [h]
  | succ k ih =>
    obtain ⟨J, hJ, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    have hJs : (triangles J).Nonempty :=
      hH.mono (triangles_mono (step_support_subset hstep))
    have hprev := ih hJ hJs
    have hcard := step_card_of_active hJs hstep
    omega

theorem evolve_terminal {n : ℕ} (G : Graph n) (k : ℕ) (hk : G.card ≤ k)
    {H : Graph n} (h : H ∈ (evolve G k).support) : triangles H = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hH
  have hcard := evolve_card_of_active G k h hH
  have hthree := three_le_card_of_triangle hH
  omega

theorem terminal_support_subset {n : ℕ} {G : Graph n}
    (h : G ∈ (terminalLaw n).support) : G ⊆ completeGraph n :=
  evolve_support_subset _ _ h

theorem terminal_edges_have_two_vertices {n : ℕ} {G : Graph n}
    (h : G ∈ (terminalLaw n).support) {e : Finset (Fin n)} (he : e ∈ G) :
    e.card = 2 :=
  mem_completeGraph.mp (terminal_support_subset h he)

theorem terminal_triangle_free {n : ℕ} {G : Graph n}
    (h : G ∈ (terminalLaw n).support) : triangles G = ∅ := by
  exact evolve_terminal (completeGraph n) (n.choose 2) (by simp) h

theorem terminal_card_le {n : ℕ} {G : Graph n}
    (h : G ∈ (terminalLaw n).support) : G.card ≤ n.choose 2 := by
  simpa using Finset.card_le_card (terminal_support_subset h)

theorem delete_triangle_injective {n : ℕ} {G : Graph n}
    {t u : Finset (Fin n)} (ht : t ∈ triangles G) (hu : u ∈ triangles G)
    (h : G \ t.powersetCard 2 = G \ u.powersetCard 2) : t = u := by
  have hedges : t.powersetCard 2 = u.powersetCard 2 := by
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp ht).2,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hu).2] using
      congrArg (fun J => G \ J) h
  exact Finset.eq_of_powersetCard_eq
    ((mem_triangles.mp ht).1.trans (mem_triangles.mp hu).1.symm)
    (by decide) (by rw [(mem_triangles.mp ht).1]; decide) hedges

theorem step_uniform_triangle {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    step G (G \ t.powersetCard 2) = ((triangles G).card : ENNReal)⁻¹ := by
  classical
  have hG : (triangles G).Nonempty := ⟨t, ht⟩
  rw [step, dite_eq_left hG, PMF.map_apply]
  rw [tsum_eq_single t]
  · simpa using PMF.uniformOfFinset_apply_of_mem hG ht
  · intro u hut
    by_cases hu : u ∈ triangles G
    · have hne : G \ t.powersetCard 2 ≠ G \ u.powersetCard 2 := by
        intro heq
        exact hut (delete_triangle_injective ht hu heq).symm
      simp [hne]
    · simp only [PMF.uniformOfFinset_apply_of_notMem hG hu, ite_self]

@[simp] theorem evolve_absorbing {n : ℕ} (G : Graph n)
    (hG : triangles G = ∅) (k : ℕ) : evolve G k = PMF.pure G := by
  induction k with
  | zero => rfl
  | succ k ih => simp [evolve, ih, step_absorbing hG]

theorem evolve_add {n : ℕ} (G : Graph n) (k l : ℕ) :
    evolve G (k + l) = (evolve G k).bind (fun H => evolve H l) := by
  induction l with
  | zero => simp [evolve]
  | succ l ih => simp [evolve, ih, PMF.bind_bind]

theorem evolve_stable {n : ℕ} (G : Graph n) (k l : ℕ) (hk : G.card ≤ k) :
    evolve G (k + l) = evolve G k := by
  rw [evolve_add]
  conv_rhs => rw [← PMF.bind_pure (evolve G k)]
  apply PMF.ext
  intro H
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro J
  by_cases hJ : J ∈ (evolve G k).support
  · rw [evolve_absorbing J (evolve_terminal G k hk hJ)]
  · have hz : evolve G k J = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hJ
    simp [hz]

end SharpTerminalLeave
end
end

end OAI
