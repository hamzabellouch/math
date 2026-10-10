import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDifferentiateIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenOperator
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Continuity and first differentiation of the origin integral on a closed rectangle. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_rectangle_integral_continuousOn (R : ℝ) (hR : 0 ≤ R)
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F (Icc 0 R ×ˢ Icc 0 1)) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (Icc 0 R) := by
  let G : ℝ → ℝ → ℂ := fun x t => F (radialClamp R x,radialClamp 1 t)
  have hG : Continuous (Function.uncurry G) := hF.comp_continuous
    (((continuous_radialClamp R).comp continuous_fst).prodMk
      ((continuous_radialClamp 1).comp continuous_snd))
    (fun p => ⟨radialClamp_mem R p.1 hR,radialClamp_mem 1 p.2 (by norm_num)⟩)
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (s := Icc (0 : ℝ) 1) hG isCompact_Icc
  apply hc.continuousOn.congr
  intro x hx
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only [G]
  rw [radialClamp_eq R x hx,radialClamp_eq 1 t ht]

theorem radial_rectangle_integral_hasDerivWithinAt (R : ℝ) (_hR : 0 ≤ R)
    (F D : ℝ × ℝ → ℂ)
    (hF : ContinuousOn F (Icc 0 R ×ˢ Icc 0 1))
    (hD : ContinuousOn D (Icc 0 R ×ˢ Icc 0 1))
    (hd : ∀ x ∈ Icc 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun y => F (y,t)) (D (x,t)) (Icc 0 R) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Icc 0 R) :
    HasDerivWithinAt (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t))
      (∫ t in Icc (0 : ℝ) 1, D (x₀,t)) (Icc 0 R) x₀ := by
  have hI (x : ℝ) (hx : x ∈ Icc 0 R) : IntegrableOn (fun t => F (x,t)) (Icc (0 : ℝ) 1) :=
    (hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hx,ht⟩)).integrableOn_compact isCompact_Icc
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hD
  let C := max B 0
  have hDC (x : ℝ) (hx : x ∈ Icc 0 R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖D (x,t)‖ ≤ C := (hB (x,t) ⟨hx,ht⟩).trans (le_max_left _ _)
  apply radial_hasDerivWithinAt_integral (fun x t => F (x,t)) (fun t => D (x₀,t))
    (Icc 0 R) x₀ C hI (hI x₀ hx₀) (hd x₀ hx₀)
  filter_upwards [self_mem_nhdsWithin] with x hx t ht
  have hne : x-x₀ ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_singleton_iff] using hx.2)
  have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => hd y hy t ht) (fun y hy => hDC y hy t ht) (convex_Icc 0 R) hx₀ hx.1
  rw [slope_def_module,norm_smul,norm_inv,inv_mul_eq_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hne)).2 (by simpa only [mul_comm] using hl)

end DefocusingNLS

end OAI
