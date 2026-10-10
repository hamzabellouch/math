import OAI.Analysis.LipschitzFree.Coordinates

namespace OAI

/-!
# Compact-uniform approximation on bounded separated spaces
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem evaluation_span_dense : Dense (Submodule.span ℝ (Set.range (delta o)) : Set (FreeSpace o)) := by
  let S := Submodule.span ℝ (Set.range (delta o))
  have hu : ∀ u : FreeSpace o, u ∈ S.topologicalClosure :=
    freeSpace_induction (fun u => u ∈ S.topologicalClosure)
      (Submodule.isClosed_topologicalClosure S) S.topologicalClosure.zero_mem
      (fun _ _ => S.topologicalClosure.add_mem)
      (fun c _ h => S.topologicalClosure.smul_mem c h)
      (fun x => Submodule.le_topologicalClosure S (Submodule.subset_span ⟨x, rfl⟩))
  intro u
  exact hu u

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem supportProjection_range (F : Finset M) :
    LinearMap.range (supportProjection o sep F).toLinearMap ≤
      Submodule.span ℝ ((delta o) '' (F : Set M)) := by
  rintro u ⟨v, rfl⟩
  change supportProjection o sep F v ∈ _
  rw [supportProjection_apply]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, hj, rfl⟩))

theorem supportProjection_finiteRank (F : Finset M) :
    Module.Finite ℝ (LinearMap.range (supportProjection o sep F).toLinearMap) :=
  (Submodule.fg_iff_finiteDimensional _).mp
    ((Submodule.fg_span (F.finite_toSet.image (delta o))).of_le (supportProjection_range o sep F))

theorem span_eventually_fixed {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ (Set.range (delta o))) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → supportProjection o sep G u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, rfl⟩ := h
    refine ⟨{x}, fun G hG => ?_⟩
    rw [supportProjection_delta, ite_eq_left (hG (Finset.mem_singleton_self _))]
  | zero => exact ⟨∅, fun _ _ => map_zero _⟩
  | add u v hu hv ihu ihv =>
    obtain ⟨F, hF⟩ := ihu
    obtain ⟨G, hG⟩ := ihv
    refine ⟨F ∪ G, fun K hK => ?_⟩
    rw [map_add, hF K (Finset.Subset.trans Finset.subset_union_left hK),
      hG K (Finset.Subset.trans Finset.subset_union_right hK)]
  | smul c u hu ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨F, fun G hG => by rw [map_smul, hF G hG]⟩

variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

include hB hb in
theorem projection_error_bound (F : Finset M) (u : FreeSpace o) :
    ‖supportProjection o sep F u - u‖ ≤ (2*B+1)*‖u‖ := by
  calc
    _ ≤ ‖supportProjection o sep F u‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ (2*B)*‖u‖ + ‖u‖ := add_le_add
      ((supportProjection o sep F).le_opNorm u |>.trans
        (mul_le_mul_of_nonneg_right (supportProjection_bound o sep F B hB hb) (norm_nonneg u))) le_rfl
    _ = _ := by ring

include hB hb in

theorem projection_pointwise (u : FreeSpace o) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp (evaluation_span_dense o u) _ (div_pos hε hK)
  obtain ⟨F, hF⟩ := span_eventually_fixed o sep hv
  refine ⟨F, fun G hG => ?_⟩
  calc
    ‖supportProjection o sep G u - u‖ =
        ‖supportProjection o sep G (u-v) - (u-v)‖ := by rw [map_sub, hF G hG]; congr 1; abel
    _ ≤ (2*B+1)*‖u-v‖ := projection_error_bound o sep B hB hb G (u-v)
    _ < ε := by
      rw [dist_eq_norm] at huv
      exact (lt_div_iff₀' hK).mp huv

include hB hb in

theorem projection_compact (C : Set (FreeSpace o)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ∀ u ∈ C,
      ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨t, _, ht, hcover⟩ := hC.finite_cover_balls (e := ε/(2*(2*B+1))) (by positivity)
  choose F hF using (fun z : FreeSpace o => projection_pointwise o sep B hB hb z (ε/2) (by positivity))
  refine ⟨ht.toFinset.biUnion F, fun G hG u hu => ?_⟩
  obtain ⟨z, hz, huz⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hzF : F z ⊆ G := (Finset.subset_biUnion_of_mem F (ht.mem_toFinset.mpr hz)).trans hG
  have hze := hF z G hzF
  have huz' : ‖u-z‖ < ε/(2*(2*B+1)) := by simpa only [Metric.mem_ball, dist_eq_norm] using huz
  have hsmall : (2*B+1)*‖u-z‖ < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(2*B+1))).mp huz'
    nlinarith
  calc
    ‖supportProjection o sep G u - u‖ =
      ‖(supportProjection o sep G (u-z) - (u-z)) + (supportProjection o sep G z - z)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖supportProjection o sep G (u-z) - (u-z)‖ + ‖supportProjection o sep G z - z‖ := norm_add_le _ _
    _ ≤ (2*B+1)*‖u-z‖ + ‖supportProjection o sep G z - z‖ :=
      add_le_add (projection_error_bound o sep B hB hb G (u-z)) le_rfl
    _ < ε := by linarith

include sep hB hb in

theorem bounded_separated_hasBAP : HasBAP (FreeSpace o) (2*B) := by
  intro C hC ε hε
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  exact ⟨supportProjection o sep F, supportProjection_finiteRank o sep F,
    supportProjection_bound o sep F B hB hb, ε/2, by linarith,
    fun u hu => (hF F le_rfl u hu).le⟩

theorem hasAP_of_hasBAP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Λ : ℝ} (h : HasBAP E Λ) : HasAP E := by
  intro C hC ε hε
  obtain ⟨T, hT, _, η, hη, he⟩ := h C hC ε hε
  exact ⟨T, hT, η, hη, he⟩

end DiscreteFree
end

end

end OAI
