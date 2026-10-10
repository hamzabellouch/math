import OAI.Analysis.BoundedHochschild.MinimalIsometricOrbit
import OAI.Analysis.BoundedHochschild.CompactConvexCenter

namespace OAI

/-!
# The separable isometric fixed-point argument

This is the specialization of the Ryll-Nardzewski argument needed for the
normal-state orbit: a linear isometric group acting on a weakly compact,
norm-separable convex set has a common fixed point.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

omit [Group G] in
private theorem minimal_weak_convex_invariant (T : G → E ≃ₗᵢ[ℂ] E)
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ L : Set (WeakSpace ℂ E), L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧ Convex ℝ L ∧
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) ∧
      ∀ D : Set (WeakSpace ℂ E), D ⊆ L → D.Nonempty → IsClosed D → Convex ℝ D →
        (∀ g, Set.MapsTo (weakIsometry (T g)) D D) → L ⊆ D := by
  classical
  let S : Set (Set (WeakSpace ℂ E)) := {L | L ⊆ C ∧ L.Nonempty ∧ IsClosed L ∧
    Convex ℝ L ∧ ∀ g, Set.MapsTo (weakIsometry (T g)) L L}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hconv, hinv⟩
  obtain ⟨L, hLC, hL⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun A hA B hB => by
          rcases hchain.total hA hB with h | h
          · exact ⟨A, hA, Set.Subset.rfl, h⟩
          · exact ⟨B, hB, h, Set.Subset.rfl⟩)
        (fun A hA => (hc hA).2.1)
        (fun A hA => hC.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (Set.sInter_subset_of_mem hA).trans (hc hA).1
    · exact isClosed_sInter (fun A hA => (hc hA).2.2.1)
    · exact convex_sInter (fun A hA => (hc hA).2.2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2.2.2 g (Set.mem_sInter.mp hx A hA)) C hCS
  refine ⟨L, hLC, hL.1.2.1, hL.1.2.2.1, hL.1.2.2.2.1, hL.1.2.2.2.2, ?_⟩
  intro D hDL hDn hDc hDv hDi
  exact hL.2 ⟨hDL.trans hLC, hDn, hDc, hDv, hDi⟩ hDL

/-- Common fixed point for the norm-separable weakly compact case. -/
theorem weakCompact_separable_isometric_fixedPoint [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' C))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨L, hLC, hLn, hLc, hLv, hLi, hLmin⟩ :=
    minimal_weak_convex_invariant T C hC hne hconv hinv
  have hLcompact : IsCompact L := hC.of_isClosed_subset hLc hLC
  obtain ⟨K, hKL, hKn, hKc, hKi, hKmin⟩ :=
    exists_minimal_compact_invariant (fun g => weakIsometry (T g)) L hLcompact hLn hLi
  have hKcompact : IsCompact K := hLcompact.of_isClosed_subset hKc hKL
  have hKsep : IsSeparable ((toWeakSpace ℂ E).symm '' K) :=
    hsep.mono (Set.image_mono (hKL.trans hLC))
  have hKnorm := minimal_isometric_orbit_normCompact T hone hmul K hKcompact hKn hKsep hKi hKmin
  have hsingle : K.Subsingleton := by
    by_contra hnonsingle
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hnonsingle
    have hnt : ((toWeakSpace ℂ E).symm '' K).Nontrivial :=
      ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, fun h => hxy ((toWeakSpace ℂ E).symm.injective h)⟩
    obtain ⟨z, hz, r, hr, hzr⟩ := compact_convex_center _ hKnorm hnt
    let B (y : K) : Set (WeakSpace ℂ E) :=
      (toWeakSpace ℂ E) '' Metric.closedBall ((toWeakSpace ℂ E).symm y.val) r
    let D : Set (WeakSpace ℂ E) := L ∩ ⋂ y : K, B y
    have hzL : toWeakSpace ℂ E z ∈ L := by
      have hcv : Convex ℝ ((toWeakSpace ℂ E).symm '' L) :=
        hLv.linear_image ((toWeakSpace ℂ E).symm.restrictScalars ℝ).toLinearMap
      obtain ⟨w, hw, heq⟩ := convexHull_min (Set.image_mono hKL) hcv hz
      simpa only [← heq, LinearEquiv.apply_symm_apply] using hw
    have hDz : toWeakSpace ℂ E z ∈ D := by
      refine ⟨hzL, Set.mem_iInter.mpr (fun y => ?_)⟩
      exact ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm] using
        (hzr _ ⟨y.val, y.property, rfl⟩), rfl⟩
    have hDc : IsClosed D := hLc.inter (isClosed_iInter (fun y => weak_closedBall _ _))
    have hDv : Convex ℝ D := hLv.inter (convex_iInter (fun y =>
      (convex_closedBall ((toWeakSpace ℂ E).symm y.val) r).linear_image
        ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap))
    have hDi : ∀ g, Set.MapsTo (weakIsometry (T g)) D D := by
      intro g a ha
      refine ⟨hLi g ha.1, Set.mem_iInter.mpr (fun y => ?_)⟩
      let b : K := ⟨weakIsometry (T g⁻¹) y.val, hKi g⁻¹ y.property⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp ha.2 b
      have hab : ‖(toWeakSpace ℂ E).symm a - (toWeakSpace ℂ E).symm b.val‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, ← heq, LinearEquiv.symm_apply_apply] using hw
      refine ⟨T g ((toWeakSpace ℂ E).symm a), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖T g ((toWeakSpace ℂ E).symm a) - (toWeakSpace ℂ E).symm y.val‖ ≤ r
      have hgb : T g ((toWeakSpace ℂ E).symm b.val) = (toWeakSpace ℂ E).symm y.val := by
        change T g (T g⁻¹ ((toWeakSpace ℂ E).symm y.val)) = _
        rw [← hmul, mul_inv_cancel, hone]
      rw [← hgb, ← map_sub, (T g).norm_map]
      exact hab
    have hLD : L ⊆ D := hLmin D Set.inter_subset_left ⟨_, hDz⟩ hDc hDv hDi
    have hdiam : Metric.diam ((toWeakSpace ℂ E).symm '' K) ≤ r := by
      apply Metric.diam_le_of_forall_dist_le_of_nonempty hnt.nonempty
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      obtain ⟨w, hw, heq⟩ := Set.mem_iInter.mp (hLD (hKL ha')).2 ⟨b', hb'⟩
      simpa only [Metric.mem_closedBall, ← heq, LinearEquiv.symm_apply_apply] using hw
    exact (not_le_of_gt hr) hdiam
  obtain ⟨x, hx⟩ := hKn
  exact ⟨x, hLC (hKL hx), fun g => hsingle (hKi g hx) hx⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
