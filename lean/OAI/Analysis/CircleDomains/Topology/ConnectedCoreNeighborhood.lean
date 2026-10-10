import OAI.Analysis.CircleDomains.Topology.SphereCoreExhaustion

namespace OAI

/-!
# Compact connected neighborhoods inside the source

A compact subset of a domain containing infinity lies strictly inside a
compact connected subset of that domain which also contains a neighborhood
of infinity. This lets successive finite Jordan cores retain earlier ones.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closure_finite_domain_with_infty (D : Set ℂ) :
    closure (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) =
      ((↑) : ℂ → Sphere) '' closure D ∪ {OnePoint.infty} := by
  apply Subset.antisymm
  · exact closure_minimal (union_subset_union_left _ (image_mono subset_closure))
      (isClosed_finite_set_with_infty isClosed_closure)
  · apply union_subset
    · exact (image_closure_subset_closure_image OnePoint.continuous_coe).trans
        (closure_mono subset_union_left)
    · exact subset_union_right.trans subset_closure

theorem isConnected_finite_domain_with_infty
    {D : Set ℂ} (hD : IsConnected D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConnected (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hunbounded : ¬ Bornology.IsBounded D := by
    intro h
    have hc := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union h
    apply NormedSpace.unbounded_univ ℝ ℂ
    apply hc.subset
    intro z _
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    · exact Or.inr (hext (le_of_lt (lt_of_not_ge hz)))
  have hinf := infty_mem_closure_image_of_unbounded hunbounded
  apply (hD.image _ OnePoint.continuous_coe.continuousOn).subset_closure subset_union_left
  exact union_subset subset_closure (singleton_subset_iff.mpr hinf)

theorem exists_compact_connected_core_neighborhood
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ P : Set Sphere, IsCompact P ∧ IsConnected P ∧ P ⊆ G ∧
      S ⊆ interior P ∧ OnePoint.infty ∈ interior P := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  let U : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_finite_domain_with_infty (hDo n) (hext.trans (hDm (Nat.zero_le n)))
  have hUm : Monotone U := fun _ _ h => union_subset_union_left _ (image_mono (hDm h))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo
    (fun p hp => hcover.symm ▸ hSG hp) hUm.directed_le
  refine ⟨K n, (hK n).1, ?_, (hK n).2, hn.trans (hDK n), hDK n (Or.inr rfl)⟩
  rw [hKdef n, ← closure_finite_domain_with_infty]
  exact (isConnected_finite_domain_with_infty (hDc n)
    (hext.trans (hDm (Nat.zero_le n)))).closure

end CircleDomainRigidity

end

end OAI
