import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicExistence
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicGlue

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem intrinsic_state_norm {γ : ℝ → M} {C t : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hC : 0 ≤ C) (hγ : IsIntrinsicGeodesicOn (E := E) γ C U) (ht : t ∈ U) :
    ‖(curveState (E := E) γ t).2‖ = C := by
  let v := (curveState (E := E) γ t).2
  obtain ⟨ε, hε, V, _, hxV, hlocal⟩ := uniformly_local_intrinsic (E := E) (γ t) (norm_nonneg v)
  obtain ⟨η, hη₀, hη⟩ := hlocal (γ t) hxV v le_rfl
  let η' : ℝ → M := fun s => η (s-t)
  let W : Set ℝ := (fun s : ℝ => s-t) ⁻¹' Metric.ball 0 ε
  have hW : IsOpen W := Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
  have htW : t ∈ W := by simpa [W] using (Metric.mem_ball_self hε : (0 : ℝ) ∈ Metric.ball 0 ε)
  have hη' : IsIntrinsicGeodesicOn (E := E) η' ‖v‖ W := hη.comp_sub
  have hstate : curveState (E := E) η' t = curveState (E := E) γ t := by
    have hh := curveState_comp_sub (γ := η) (t := t) (a := t) (by
      simpa only [sub_self] using (((hη.1 0 (Metric.mem_ball_self hε)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))).mdifferentiableAt (by simp)))
    change curveState (E := E) (fun s => η (s-t)) t = _
    rw [hh, sub_self, hη₀]
    rfl
  have he := intrinsic_germ_unique_on (hU.inter hW)
    (hγ.1.mono inter_subset_left) (hη'.1.mono inter_subset_right) ⟨ht, htW⟩
    hC (norm_nonneg v) (hγ.2 t ht) (hη'.2 t htW) hstate.symm
  exact (intrinsic_speed_eq_of_germ (hγ.at hU ht) (hη'.at hW htW) he).symm

 theorem compact_uniform_intrinsic [CompactSpace M] {C : ℝ} (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε) := by
  classical
  choose δ hδ V hV hmem hlocal using fun x : M => uniformly_local_intrinsic (E := E) x hC
  have hcover : (univ : Set M) ⊆ ⋃ x, V x := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  have hmin : ∀ F : Finset M, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, ε ≤ δ x := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x _ _ ih =>
      obtain ⟨ε, hε, hb⟩ := ih
      refine ⟨min ε (δ x), lt_min hε (hδ x), ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb y hy)
  obtain ⟨ε, hε, hεδ⟩ := hmin F
  refine ⟨ε, hε, ?_⟩
  intro y v hv
  obtain ⟨x, hxF, hyV⟩ := mem_iUnion₂.mp (hF (mem_univ y))
  obtain ⟨γ, hγ₀, hγ⟩ := hlocal x y hyV v hv
  refine ⟨γ, hγ₀, hγ.mono ?_⟩
  intro t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have he := hεδ x hxF
  exact ⟨lt_of_le_of_lt (neg_le_neg he) ht.1, ht.2.trans_le he⟩

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
