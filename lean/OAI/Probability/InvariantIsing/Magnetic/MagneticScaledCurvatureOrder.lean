import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledBounds
import OAI.Probability.InvariantIsing.Magnetic.MagneticBoundedInverseComparison

namespace OAI

/-! Radial comparison of the actual inverse curvatures. The proof follows
all finite Gaussian levels, starting from α(1-s²) at the Ising terminal. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma magneticScaledClosedCurvature_mono_of_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      magneticScaledClosedCurvature L hL α ζ (0, u) ≤
        magneticScaledClosedCurvature L hL β ζ (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature L hL α ζ (v, s) ≤
      magneticScaledClosedCurvature L hL β ζ (v, s) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hall := inverse_curvature_parabolic_comparison_bound hv
    (show 0 ≤ (β : ℝ) * ζ from mul_nonneg β.coe_nonneg hζ)
    (mul_le_mul_of_nonneg_right (show (α : ℝ) ≤ (β : ℝ) from hαβ) hζ)
    (magneticScaledClosedCurvature L hL α ζ) (magneticScaledClosedTime L hL α ζ)
    (magneticScaledClosedSlope L hL α ζ) (magneticScaledClosedSecond L hL α ζ)
    (magneticScaledClosedCurvature L hL β ζ) (magneticScaledClosedTime L hL β ζ)
    (magneticScaledClosedSlope L hL β ζ) (magneticScaledClosedSecond L hL β ζ)
    ((magneticScaledClosedCurvature_continuousOn L hL hL1 α hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((magneticScaledClosedCurvature_continuousOn L hL hL1 β hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (magneticScaledClosedCurvature_hasDerivAt_time L hL hα hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (magneticScaledClosedCurvature_hasDerivAt_time L hL hβ hζ ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => magneticScaledClosedCurvature_hasDerivAt_spin L hL α hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledClosedCurvature_hasDerivAt_spin L hL β hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledClosedSlope_hasDerivAt_spin L hL α hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledClosedSlope_hasDerivAt_spin L hL β hζ (abs_lt.mpr hu) t)
    (fun p hp => (magneticScaledClosedCurvature_mem_interval L hL hL1 α hζ hζ1 p hp.2).1)
    (fun p hp => (magneticScaledClosedCurvature_mem_interval L hL hL1 β hζ hζ1 p hp.2).1)
    (fun p hp => (magneticScaledClosedCurvature_mem_interval L hL hL1 α hζ hζ1 p hp.2).2)
    (fun p _ => magneticScaledClosedCurvature_weighted_second_bound L hL hL1 α hζ hζ1 p)
    (fun t _ => by
      obtain ⟨hαm, hαp⟩ := magneticScaledClosedCurvature_endpoints L hL α ζ t
      obtain ⟨hβm, hβp⟩ := magneticScaledClosedCurvature_endpoints L hL β ζ t
      exact ⟨hαm, hβm, hαp, hβp⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

theorem magneticScaledClosedCurvature_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature L hL α ζ (v, s) ≤
      magneticScaledClosedCurvature L hL β ζ (v, s) := by
  induction L generalizing ζ v s with
  | nil =>
    apply magneticScaledClosedCurvature_mono_of_initial [] hL hL1 hα hαβ hζ hζ1 ?_ hv hs
    intro u hu
    rw [magneticScaledClosedCurvature_nil_initial hζ hu,
      magneticScaledClosedCurvature_nil_initial hζ hu]
    have hu2 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    exact mul_le_mul_of_nonneg_right (show (α : ℝ) ≤ (β : ℝ) from hαβ) hu2
  | cons av L ih =>
    apply magneticScaledClosedCurvature_mono_of_initial (av :: L) hL hL1 hα hαβ hζ hζ1 ?_ hv hs
    intro u hu
    rw [magneticScaledClosedCurvature_cons_initial, magneticScaledClosedCurvature_cons_initial]
    exact ih (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
      (fun bv hb => hL1 bv (List.mem_cons_of_mem av hb))
      (hL av List.mem_cons_self).le (hL1 av List.mem_cons_self) av.2.property hu

end InvariantIsing

end

end OAI
