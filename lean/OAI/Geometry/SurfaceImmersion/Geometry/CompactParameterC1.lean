import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! Compact C1 bounds for a smooth parameter family and its spatial slices. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {P X V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_parameter_C1 {A : Set P} {K : Set X} (hA : IsCompact A) (hK : IsCompact K)
    {F : P × X → V} (hF : ∀ z ∈ A ×ˢ K, ContDiffAt ℝ ∞ F z) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ a ∈ A, ∀ x ∈ K,
      ‖F (a,x)‖ ≤ D ∧ ‖fderiv ℝ (fun y => F (a,y)) x‖ ≤ D := by
  have hc : ContinuousOn (fun z => (F z,fderiv ℝ F z)) (A ×ˢ K) := by
    intro z hz
    exact ((hF z hz).continuousAt.prodMk ((hF z hz).continuousAt_fderiv (by simp))).continuousWithinAt
  obtain ⟨C,hC⟩ := (hA.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro a ha x hx
  have hb := (hC (a,x) ⟨ha,hx⟩).trans (le_max_right 1 C)
  have hv := (norm_fst_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  have hd := (norm_snd_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  refine ⟨hv,?_⟩
  have hpair : HasFDerivAt (fun y : X => (a,y)) (ContinuousLinearMap.inr ℝ P X) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have he := ((hF (a,x) ⟨ha,hx⟩).differentiableAt (by simp)).hasFDerivAt.comp x hpair
  change ‖fderiv ℝ (F ∘ Prod.mk a) x‖ ≤ max 1 C
  rw [he.fderiv]
  calc
    _ ≤ ‖fderiv ℝ F (a,x)‖*‖ContinuousLinearMap.inr ℝ P X‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F (a,x)‖*1 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one ℝ P X) (norm_nonneg _)
    _ ≤ max 1 C := by simpa only [mul_one] using hd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
