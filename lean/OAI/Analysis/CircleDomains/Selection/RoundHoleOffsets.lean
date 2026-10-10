import OAI.Analysis.CircleDomains.Topology.JordanExteriors

namespace OAI

/-! A single positive offset works for a finite family of disjoint round
holes. The enlarged closed holes remain disjoint and inside the given
open region, including when an original hole has radius zero. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_round_hole_offset
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {U : Set ℂ} (hU : IsOpen U) (hin : ∀ i, closedBall (c i) (r i) ⊆ U) :
    ∃ ε > 0, ∀ ρ ∈ Ioc (0 : ℝ) ε,
      (∀ i, closedBall (c i) (r i + ρ) ⊆ U) ∧
      Pairwise (Disjoint on fun i => closedBall (c i) (r i + ρ)) := by
  classical
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (closedBall (c i) (r i))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_closedBall isClosed_closedBall (hd hij)
  obtain ⟨V, hV, hVdisj⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (closedBall (c i) (r i)))
  have he (i : I) : ∃ δ > 0, closedBall (c i) (r i + δ) ⊆ V i ∩ U := by
    obtain ⟨δ, hδ, hs⟩ := (isCompact_closedBall (c i) (r i)).exists_cthickening_subset_open
      ((hV i).1.inter hU) (fun z hz => ⟨(hV i).2 hz, hin i hz⟩)
    refine ⟨δ, hδ, ?_⟩
    simpa only [cthickening_closedBall hδ.le (hr i), add_comm δ] using hs
  choose δ hδ hδsub using he
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let ε := S.min' hS
  have hε : 0 < ε := by
    have hm : ε ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hδ i
  have hεi (i : I) : ε ≤ δ i :=
    Finset.min'_le S (δ i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨ε, hε, ?_⟩
  intro ρ hρ
  have hsub (i : I) : closedBall (c i) (r i + ρ) ⊆ V i ∩ U :=
    (closedBall_subset_closedBall (add_le_add le_rfl (hρ.2.trans (hεi i)))).trans (hδsub i)
  exact ⟨fun i z hz => (hsub i hz).2, fun i j hij => (hVdisj hij).mono
    (fun z hz => (hsub i hz).1) (fun z hz => (hsub j hz).1)⟩

end CircleDomainRigidity

end

end OAI
