import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyState
import OAI.Combinatorics.KMedian.Geometry.GreedyPacking

namespace OAI

section
section
namespace MetricKMedian.Completion
open Finset PhysicalPotential CopyState
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X]

theorem complete (Δ : ℕ) {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1)
    (location : F → X) (client : J → X) (R : J → ℝ) (hR : ∀ j, 0 ≤ R j)
    (A : Finset (Copy (F := F) Δ)) (S₀ : J → Finset (Copy (F := F) Δ))
    (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i∈S₀ j → dist (client j) (location i.1) ≤ R j)
    (hbackup : ∀ j, (¬∃ f ∈ integral Δ A, dist (client j) (location f) ≤ 5*R j) → S₀ j ⊆ A) :
    ∃ O : Finset F, integral Δ A ⊆ O ∧ (O.card:ℝ) ≤ mass g A ∧
      ∀ j, ∃ f∈O, dist (client j) (location f) ≤ 5*R j := by
  classical
  let Q := integral Δ A
  let U := univ.filter (fun j => ¬∃ f∈Q, dist (client j) (location f) ≤ 5*R j)
  have hS : ∀ j, (S₀ j).Nonempty := by
    intro j
    apply nonempty_iff_ne_empty.mpr
    intro he
    have hh := hm j
    rw [he,mass,card_empty,Nat.cast_zero,mul_zero] at hh
    norm_num at hh
  have hB : ∀ j∈U, S₀ j ⊆ A \ resets Δ Q := by
    intro j hj i hi
    have hn := (mem_filter.mp hj).2
    refine mem_sdiff.mpr ⟨hbackup j hn hi,?_⟩
    intro hir
    have hif := (mem_resets Δ Q i).mp hir
    exact hn ⟨i.1,hif,(hd j i hi).trans (by linarith only [hR j])⟩
  obtain ⟨C,hCU,hdis,hcover⟩ := radius_packing U R S₀ (fun j _ => hS j)
  let pick : J → Copy (F := F) Δ := fun j => (hS j).choose
  have hpick : ∀ j, pick j∈S₀ j := fun j => (hS j).choose_spec
  let O : Finset F := Q ∪ C.image (fun j => (pick j).1)
  have hreserve : resets Δ Q ⊆ A := by
    intro i hi
    exact (mem_integral Δ A i.1).mp ((mem_resets Δ Q i).mp hi)
      ((mem_slots Δ i.1 i).mpr rfl)
  have hcount : (C.card:ℝ) ≤ mass g A-(Q.card:ℝ) := by
    have hh := packing_mass hg C S₀ (A \ resets Δ Q)
      (fun j hj => hB j (hCU hj)) hdis (fun j _ => (hm j).ge)
    rw [mass_sdiff g hreserve,reset_mass Δ Q hunit] at hh
    exact hh
  refine ⟨O,subset_union_left,?_,?_⟩
  · have hh : (O.card:ℝ) ≤ (Q.card:ℝ)+(C.card:ℝ) := by
      exact_mod_cast (card_union_le Q (C.image (fun j => (pick j).1))).trans
        (Nat.add_le_add_left card_image_le Q.card)
    linarith only [hh,hcount]
  · intro j
    by_cases hj : j∈U
    · obtain ⟨a,ha,hRa,hinter⟩ := hcover j hj
      refine ⟨(pick a).1,mem_union_right Q (mem_image.mpr ⟨a,ha,rfl⟩),?_⟩
      have hh := packed_connection client (fun i : Copy (F := F) Δ => location i.1) R S₀
        hd hRa hinter (hpick a)
      exact hh.trans (by linarith only [hR j])
    · have hex : ∃ f∈Q, dist (client j) (location f) ≤ 5*R j := by
        simpa only [U,mem_filter,mem_univ,true_and,not_not] using hj
      obtain ⟨f,hf,hfd⟩ := hex
      exact ⟨f,mem_union_left _ hf,hfd⟩

end MetricKMedian.Completion
end
end

end OAI
