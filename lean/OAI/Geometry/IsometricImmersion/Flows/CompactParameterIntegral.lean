import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u
namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def compactParameterIntegral (H : Coord × ℝ → F) (p : Coord) : F :=
  ∫ s in Icc (0 : ℝ) 1, H (p,s)

def compactParameterPartial (H : Coord × ℝ → F) (q : Coord × ℝ) : Coord →L[ℝ] F :=
  (fderiv ℝ H q).comp (ContinuousLinearMap.inl ℝ Coord ℝ)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem parameter_slice_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D)
    {p : Coord} (hp : p ∈ U) : ContinuousOn (fun s => H (p,s)) (Icc (0 : ℝ) 1) :=
  hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => hUD ⟨hp,hs⟩)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem exists_local_parameter_norm_bound
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    ∃ e B : ℝ, 0 < e ∧ 0 ≤ B ∧ Metric.ball p e ⊆ U ∧
      ∀ x ∈ Metric.ball p e, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (x,s)‖ ≤ B := by
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let K := Metric.closedBall p (e/2) ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall p (e/2)).prod isCompact_Icc
  have hKD : K ⊆ D := by
    intro q hq
    exact hUD ⟨hball (Metric.closedBall_subset_ball (half_lt_self he) hq.1),hq.2⟩
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hH.mono hKD)
  refine ⟨e/2,max B 0,half_pos he,le_max_right _ _,?_,?_⟩
  · intro x hx
    exact hball ((Metric.ball_subset_ball (half_le_self he.le)) hx)
  · intro x hx s hs
    exact (hB (x,s) ⟨Metric.ball_subset_closedBall hx,hs⟩).trans (le_max_left _ _)

omit [CompleteSpace F] in
theorem compactParameterIntegral_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) : ContinuousOn (compactParameterIntegral H) U := by
  intro p hp
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hH hU hUD hp
  have hmeas : ∀ᶠ x in 𝓝 p, AEStronglyMeasurable (fun s => H (x,s))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  have hdom : ∀ᶠ x in 𝓝 p, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ‖H (x,s)‖ ≤ B := by
    filter_upwards [Metric.ball_mem_nhds p he] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound x hx s hs
  have hint : Integrable (fun _ : ℝ => B) (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ContinuousAt (fun x => H (x,s)) p := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hH.continuousAt (hD.mem_nhds (hUD ⟨hp,hs⟩))).comp
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_of_dominated hmeas hdom hint hpoint).continuousWithinAt

omit [CompleteSpace F] in
theorem compactParameterPartial_contDiffOn
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hD : IsOpen D) (n : ℕ)
    (hH : ContDiffOn ℝ (n+1 : ℕ) H D) :
    ContDiffOn ℝ n (compactParameterPartial H) D := by
  have hd : ContDiffOn ℝ n (fderiv ℝ H) D := hH.fderiv_of_isOpen hD (by simp)
  exact hd.clm_comp contDiffOn_const

omit [CompleteSpace F] in
theorem compactParameter_slice_hasFDerivAt
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hH : ContDiffOn ℝ 1 H D)
    (hD : IsOpen D) {p : Coord} {s : ℝ} (hp : (p,s) ∈ D) :
    HasFDerivAt (fun x => H (x,s)) (compactParameterPartial H (p,s)) p := by
  have hd := ((hH.contDiffAt (hD.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hi : HasFDerivAt (fun x : Coord => (x,s)) (ContinuousLinearMap.inl ℝ Coord ℝ) p :=
    hasFDerivAt_prodMk_left p s
  exact hd.comp p hi

omit [CompleteSpace F] in
theorem compactParameterIntegral_hasFDerivAt
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ 1 H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    HasFDerivAt (compactParameterIntegral H)
      (compactParameterIntegral (compactParameterPartial H) p) p := by
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH).continuousOn
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hpart hU hUD hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (bound := fun _ => B)
    (s := Metric.ball p e) (F' := fun x s => compactParameterPartial H (x,s))
    (Metric.ball_mem_nhds p he)
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH.continuousOn hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · exact (parameter_slice_continuousOn hH.continuousOn hUD hp).integrableOn_compact isCompact_Icc
  · exact ((parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact hbound x hx s hs
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact compactParameter_slice_hasFDerivAt hH hD (hUD ⟨hball hx,hs⟩)

theorem compactParameterIntegral_contDiffOn_finite (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)},
      ContDiffOn ℝ n H D → IsOpen D → IsOpen U →
      U ×ˢ Icc (0 : ℝ) 1 ⊆ D → ContDiffOn ℝ n (compactParameterIntegral H) U := by
  induction n with
  | zero =>
    intro F _ _ _ H U D hH hD hU hUD
    simpa only [Nat.cast_zero,contDiffOn_zero] using
      compactParameterIntegral_continuousOn hH.continuousOn hD hU hUD
  | succ n ih =>
    intro F _ _ _ H U D hH hD hU hUD
    have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by exact_mod_cast (show 1 ≤ n+1 by omega))
    have hd (p : Coord) (hp : p ∈ U) := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
    have hpart : ContDiffOn ℝ n (compactParameterPartial H) D :=
      compactParameterPartial_contDiffOn hD n hH
    have hmeanPart : ContDiffOn ℝ n (compactParameterIntegral (compactParameterPartial H)) U :=
      ih hpart hD hU hUD
    have hs : ContDiffOn ℝ ((n : ℕ∞ω)+1) (compactParameterIntegral H) U := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
      exact hmeanPart.congr (fun p hp => (hd p hp).fderiv)
    simpa only [Nat.cast_add,Nat.cast_one] using hs

theorem compactParameterIntegral_contDiffOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) :
    ContDiffOn ℝ ∞ (compactParameterIntegral H) U :=
  contDiffOn_infty.mpr (fun n => compactParameterIntegral_contDiffOn_finite n
    (hH.of_le (WithTop.coe_le_coe.mpr le_top)) hD hU hUD)

end SmoothLocal.Analytic

end

end OAI
