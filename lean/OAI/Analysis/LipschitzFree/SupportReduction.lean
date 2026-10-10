import OAI.Analysis.LipschitzFree.CompactApproximation

namespace OAI

/-!
# Finite-rank operators admit finite-support perturbations
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem projection_span_fixed (F : Finset M) {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ ((delta o) '' (F : Set M))) :
    supportProjection o sep F u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, hx, rfl⟩ := h
    rw [supportProjection_delta, ite_eq_left (show x ∈ F from hx)]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, ih]

theorem projection_idempotent (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F (supportProjection o sep F u) = supportProjection o sep F u :=
  projection_span_fixed o sep F (supportProjection_range o sep F ⟨u, rfl⟩)

theorem projection_comp_finiteRank (F : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o) :
    Module.Finite ℝ (LinearMap.range ((supportProjection o sep F).comp T).toLinearMap) := by
  have := supportProjection_finiteRank o sep F
  exact Module.Finite.of_injective
    (Submodule.inclusion (LinearMap.range_comp_le_range T.toLinearMap (supportProjection o sep F).toLinearMap))
    (Submodule.inclusion_injective _)

theorem projection_finiteRank_approx (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖(supportProjection o sep G).comp T - T‖ < ε := by
  let Y := LinearMap.range T.toLinearMap
  let J : Y →L[ℝ] FreeSpace o := Y.subtypeL
  let C : Set (FreeSpace o) := J '' Metric.closedBall (0 : Y) ‖T‖
  have hC : IsCompact C := (isCompact_closedBall (0 : Y) ‖T‖).image J.continuous
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  refine ⟨F, fun G hG => ?_⟩
  have hnorm : ‖(supportProjection o sep G).comp T - T‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    have hTu : T u ∈ C := by
      refine ⟨⟨T u, ⟨u, rfl⟩⟩, ?_, rfl⟩
      change dist (T u) 0 ≤ ‖T‖
      simpa only [dist_zero_right, hu, mul_one] using T.le_opNorm u
    exact (hF G hG (T u) hTu).le
  linarith

theorem finite_support_reduction (B p : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hb : ∀ x, dist x o ≤ B) (A : Finset M)
    (T₀ : FreeSpace o →L[ℝ] FreeSpace o)
    (hfinite : Module.Finite ℝ (LinearMap.range T₀.toLinearMap)) (hnorm : ‖T₀‖ ≤ p)
    (hanchor : ∀ a ∈ A, ‖T₀ (delta o a) - delta o a‖ < 1/2) :
    ∃ (S : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o), o ∈ S ∧
      Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧ ‖T‖ ≤ 2*p ∧
      (∀ u, supportProjection o sep S (T u) = T u) ∧
      ∀ a ∈ A, ‖T (delta o a) - delta o a‖ < 1 := by
  let ε := min p (1/(2*(B+1)))
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  obtain ⟨F, hF⟩ := projection_finiteRank_approx o sep B hB hb T₀ hfinite ε hε
  let S := insert o F
  let T := (supportProjection o sep S).comp T₀
  have hdiff : ‖T-T₀‖ < ε := hF S (Finset.subset_insert _ _)
  have hn : ‖T‖ ≤ 2*p := by
    have hs := norm_add_le (T-T₀) T₀
    rw [sub_add_cancel] at hs
    have hεp : ε ≤ p := min_le_left _ _
    linarith
  refine ⟨S, T, Finset.mem_insert_self _ _, projection_comp_finiteRank o sep S T₀,
    hn, fun u => projection_idempotent o sep S (T₀ u), fun a ha => ?_⟩
  have hda := delta_norm o a
  have he : ‖(T-T₀) (delta o a)‖ ≤ ε*B := by
    calc
      _ ≤ ‖T-T₀‖ * ‖delta o a‖ := (T-T₀).le_opNorm _
      _ ≤ ε * B := mul_le_mul hdiff.le (by simpa using hb a) (norm_nonneg _) hε.le
  have hfrac : ε*B < 1/2 := by
    have hh : ε ≤ 1/(2*(B+1)) := min_le_right _ _
    have hden : 0 < 2*(B+1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hh
    nlinarith
  calc
    ‖T (delta o a) - delta o a‖ =
      ‖(T-T₀) (delta o a) + (T₀ (delta o a) - delta o a)‖ := by
        simp only [sub_apply]; congr 1; abel
    _ ≤ ‖(T-T₀) (delta o a)‖ + ‖T₀ (delta o a) - delta o a‖ := norm_add_le _ _
    _ < 1 := by linarith [hanchor a ha]

end DiscreteFree
end

end

end OAI
