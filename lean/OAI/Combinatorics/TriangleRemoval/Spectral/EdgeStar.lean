import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Spectral.StarInclusion

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

def edgeStar {n : ℕ} (G : Graph n) (u : Fin n) : Finset G :=
  Finset.univ.filter (fun e => u ∈ e.val)

@[simp] theorem mem_edgeStar {n : ℕ} (G : Graph n) (u : Fin n) (e : G) :
    e ∈ edgeStar G u ↔ u ∈ e.val := by simp [edgeStar]

def neighborEdge {n : ℕ} (G : Graph n) (u : Fin n) (v : neighbors G u) : edgeStar G u :=
  ⟨⟨{u,v.val},(Finset.mem_filter.mp v.property).2⟩,by simp⟩

theorem neighborEdge_injective {n : ℕ} (G : Graph n) (u : Fin n) :
    Function.Injective (neighborEdge G u) := by
  intro v w h
  have he : ({u,v.val} : Finset (Fin n)) = {u,w.val} := congrArg (fun e => e.val.val) h
  have hv : v.val ∈ ({u,w.val} : Finset (Fin n)) := he ▸ (by simp)
  have hw : w.val ∈ ({u,v.val} : Finset (Fin n)) := he.symm ▸ (by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
  apply Subtype.ext
  rcases hv with hv | hv
  · rcases hw with hw | hw
    · exact hv.trans hw.symm
    · exact hw.symm
  · exact hv

theorem neighborEdge_surjective {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    Function.Surjective (neighborEdge G u) := by
  intro e
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (hG e.val.property))
  have hu : u ∈ e.val.val := (mem_edgeStar G u e.val).mp e.property
  rw [he] at hu
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  have hm : ({a,b} : Finset (Fin n)) ∈ G := he ▸ e.val.property
  rcases hu with rfl | rfl
  · refine ⟨⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm
  · refine ⟨⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,?_⟩
    · simpa only [Finset.pair_comm] using hm
    · apply Subtype.ext
      apply Subtype.ext
      exact (Finset.pair_comm _ _).trans he.symm

noncomputable def neighborEdgeEquiv {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    neighbors G u ≃ edgeStar G u :=
  Equiv.ofBijective (neighborEdge G u) ⟨neighborEdge_injective G u,neighborEdge_surjective G hG u⟩

theorem edgeStar_card {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    (edgeStar G u).card = currentDegree G u := by
  have h := Fintype.card_congr (neighborEdgeEquiv G hG u)
  simpa only [Fintype.card_coe,currentDegree] using h.symm

theorem edgeStar_exact_overlap {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (e : G) :
    (Finset.univ.filter fun u => e ∈ edgeStar G u).card = 2 := by
  have he : (Finset.univ.filter fun u => e ∈ edgeStar G u) = e.val := by
    ext u
    simp
  rw [he]
  exact mem_completeGraph.mp (hG e.property)

open scoped Matrix.Norms.L2Operator in

theorem graph_star_error_norm {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : (u : Fin n) → Matrix (edgeStar G u) (edgeStar G u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) (hlocal : ∀ u, ‖M u‖ ≤ ε) :
    ‖∑ u, extendStar (edgeStar G u) (M u)‖ ≤ 2*ε := by
  apply sum_star_norm_bound _ _ hM ε 2 hε (by norm_num) hlocal
  intro e
  rw [edgeStar_exact_overlap G hG e]
  norm_num

end SharpTerminalLeave

end
end

end OAI
