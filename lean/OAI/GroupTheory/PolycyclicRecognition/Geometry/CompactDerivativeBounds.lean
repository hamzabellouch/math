import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Uniform derivative bounds on a compact family of endpoint maps -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem compact_family_derivative_bounds
    {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P × V → W) (hf : ContDiff ℝ 2 f)
    {S : Set P} (hS : IsCompact S) (R : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ p ∈ S, ∀ v, ‖v‖ ≤ R → ‖fderiv ℝ (fun w => f (p, w)) v‖ ≤ L) ∧
      ∀ p ∈ S, ∀ v w, ‖v‖ ≤ R → ‖w‖ ≤ R →
        ‖fderiv ℝ (fun u => f (p, u)) v - fderiv ℝ (fun u => f (p, u)) w‖ ≤
          L * dist v w := by
  let df : P × V → V →L[ℝ] W := fun z => fderiv ℝ (fun w => f (z.1, w)) z.2
  have hdf : ContDiff ℝ 1 df := by
    apply ContDiff.fderiv (g := Prod.snd)
      (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    norm_num
  let K := S ×ˢ closedBall (0 : V) R
  have hK : IsCompact K := hS.prod (isCompact_closedBall _ _)
  obtain ⟨C₁, hC₁, hb₁⟩ := (hK.image hdf.continuous).isBounded.exists_pos_norm_le
  obtain ⟨C₂, hC₂, hb₂⟩ := (hK.image (hdf.continuous_fderiv one_ne_zero)).isBounded.exists_pos_norm_le
  let L := max 1 (max C₁ C₂)
  have hL₁ : C₁ ≤ L := (le_max_left C₁ C₂).trans (le_max_right 1 _)
  have hL₂ : C₂ ≤ L := (le_max_right C₁ C₂).trans (le_max_right 1 _)
  refine ⟨L, le_max_left _ _, ?_, ?_⟩
  · intro p hp v hv
    exact (hb₁ _ ⟨(p, v), ⟨hp, by simpa using hv⟩, rfl⟩).trans hL₁
  · intro p hp v w hv hw
    have hder (u : V) : HasFDerivAt (fun x => df (p, x))
        ((fderiv ℝ df (p, u)).comp (ContinuousLinearMap.inr ℝ P V)) u := by
      exact (hdf.differentiable one_ne_zero (p, u)).hasFDerivAt.comp u
        ((hasFDerivAt_const p u).prodMk (hasFDerivAt_id u))
    have hbound (u : V) (hu : u ∈ closedBall 0 R) :
        ‖(fderiv ℝ df (p, u)).comp (ContinuousLinearMap.inr ℝ P V)‖ ≤ L := by
      calc
        _ ≤ ‖fderiv ℝ df (p, u)‖ * ‖ContinuousLinearMap.inr ℝ P V‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ df (p, u)‖ * 1 := mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_inr_le_one ℝ P V) (norm_nonneg (fderiv ℝ df (p, u)))
        _ ≤ L := by simpa using (hb₂ _ ⟨(p, u), ⟨hp, hu⟩, rfl⟩).trans hL₂
    have hh := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun u _ => (hder u).hasFDerivWithinAt) hbound
      (by simpa using hw) (by simpa using hv)
    simpa only [df, dist_eq_norm] using hh

end PolycyclicRecognition

end

end OAI
