import OAI.Probability.RadialTransition.IdealLimit

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma branch_joint_continuous {Q : Pressure}
    (hQ : ContinuousOn (onParameters Q) positiveParameters) (a : ℝ) :
    ContinuousOn (fun z : ℝ × Parameter => onParameters (attractionBranch Q a z.1) z.2)
      (univ ×ˢ positiveParameters) := by
  have hc0 : Continuous (fun z : ℝ × Parameter => z.2 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_snd
  have hc1 : Continuous (fun z : ℝ × Parameter => z.2 1) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_snd
  have hmap : Continuous (fun z : ℝ × Parameter => parameter (z.2 0) (z.2 1+z.2 0*a*z.1)) :=
    continuous_parameter _ _ hc0 (hc1.add ((hc0.mul_const a).mul continuous_fst))
  have hcomp := hQ.comp (s := univ ×ˢ positiveParameters) hmap.continuousOn (by
    intro z hz
    change 0 < z.2 0
    exact hz.2)
  exact hcomp.sub (((hc0.mul_const a).div_const 2).mul (continuous_fst.pow 2)).continuousOn

lemma ideal_supportSet_generated {Q : Pressure} {a U r : ℝ} {x : Parameter}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q)) (ha : 0 < a)
    (hactive : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u)
    (hr : 0 < r) (hxr : 2*r < x 0)
    (hlocal : ∀ y ∈ Metric.closedBall x r, ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (y 0) (y 1) u) :
    supportSet (onParameters (idealAttraction Q a)) positiveParameters x =
      closure (convexHull ℝ {v : Parameter | ∃ u ∈ Icc (0:ℝ) U,
        ActiveShift Q a (x 0) (x 1) u ∧ ∃ e : ℝ,
        pressureSupport Q (x 0) (x 1+x 0*a*u) e u ∧ v=parameter (e+a*u^2/2) u}) := by
  have hball : Metric.closedBall x (2*r) ⊆ positiveParameters := by
    intro y hy
    have hcoord := parameter_coord_abs_le (y-x) 0
    have hn := Metric.mem_closedBall.mp hy
    rw [dist_eq_norm] at hn
    simp only [PiLp.sub_apply] at hcoord
    have hh := (abs_le.mp (hcoord.trans hn)).1
    change 0 < y 0
    linarith
  have hx : 0 < x 0 := by linarith
  have hP := convexOn_idealAttraction hQ hactive
  have hformula := supportSet_envelope_closedHull isOpen_positiveParameters isCompact_Icc hr hball
    (fun u _ => convexOn_attractionBranch hQ a u)
    ((branch_joint_continuous (hQ.continuousOn isOpen_positiveParameters) a).mono
      (prod_mono (subset_univ _) Subset.rfl))
    (hP.continuousOn isOpen_positiveParameters)
    (fun u _ y hy => by
      obtain ⟨v, hv⟩ := hactive (y 0) (y 1) hy
      change attractionBranch Q a u (y 0) (y 1) ≤ idealAttraction Q a (y 0) (y 1)
      rw [idealAttraction_eq_of_active hv]
      exact hv u)
    (fun y hy => by
      obtain ⟨u, hub, hu⟩ := hlocal y hy
      exact ⟨u, hub, (idealAttraction_eq_of_active hu).symm⟩)
  rw [hformula]
  congr 2
  ext v
  constructor
  · rintro ⟨u, hub, heq, hv⟩
    have hu : ActiveShift Q a (x 0) (x 1) u := by
      intro w
      change attractionBranch Q a u (x 0) (x 1) = idealAttraction Q a (x 0) (x 1) at heq
      rw [heq]
      obtain ⟨z, hz⟩ := hactive (x 0) (x 1) hx
      exact le_csSup (ideal_bddAbove_of_active hz) (mem_range_self w)
    have hs := support_of_attractionBranch (pressureSupport_iff.mpr hv)
    have hd := active_support_density ha hx hu hs
    refine ⟨u, hub, hu, v 0-a*u*(v 1)+a*u^2/2, ?_, ?_⟩
    · simpa only [hd] using hs
    · ext i
      fin_cases i
      · change v 0 = v 0-a*u*(v 1)+a*u^2/2+a*u^2/2
        rw [hd]
        ring
      · change v 1 = u
        exact hd
  · rintro ⟨u, hub, hu, e, hs, rfl⟩
    refine ⟨u, hub, (idealAttraction_eq_of_active hu).symm, ?_⟩
    have hs' : pressureSupport (attractionBranch Q a u) (x 0) (x 1) (e+a*u^2/2) u := by
      convert support_attractionBranch hs using 1
      ring
    exact pressureSupport_iff.mp hs'

lemma ideal_increment_bound {Q : Pressure} {a β h U u : ℝ}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q)) (ha : 0 < a) (hβ : 0 < β)
    (hu : ActiveShift Q a β h u) (hub : u ∈ Icc (0:ℝ) U) :
    0 ≤ idealAttraction Q a β h-Q β h ∧ idealAttraction Q a β h-Q β h ≤ β*a/2*U^2 := by
  obtain ⟨v, hv⟩ := supportSet_nonempty isOpen_positiveParameters hQ
    (show parameter β (h+β*a*u) ∈ positiveParameters from hβ)
  have hs := pressureSupport_iff.mpr hv
  simp only [parameter_zero, parameter_one] at hs
  have hd := active_support_density ha hβ hu hs
  have hh := hs β h hβ
  rw [hd] at hh
  have hz := hu 0
  simp only [attractionBranch, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hz
  rw [idealAttraction_eq_of_active hu]
  dsimp only [attractionBranch] at hh hz ⊢
  have hsq : u^2 ≤ U^2 := sq_le_sq₀ hub.1 (hub.1.trans hub.2) |>.mpr hub.2
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ β*a/2 by positivity)
  constructor <;> nlinarith

end RadialTransition
end

end OAI
