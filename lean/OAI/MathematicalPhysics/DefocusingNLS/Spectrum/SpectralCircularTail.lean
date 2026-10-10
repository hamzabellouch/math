import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailEquation
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! The backward weighted integral for the two circular spectral channels. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

abbrev CircularTailSpace := (ℝ →ᵇ ℂ × ℂ) × (ℝ →ᵇ ℂ × ℂ)

noncomputable def circularTail (κ : ℝ) (hκ : 0 < κ) (g : CircularTailSpace) : CircularTailSpace :=
  (boundedRadialExteriorTail κ hκ g.1,star (boundedRadialExteriorTail κ hκ (star g.2)))

theorem circularTail_norm (κ : ℝ) (hκ : 0 < κ) (g : CircularTailSpace) :
    ‖circularTail κ hκ g‖ ≤ ‖g‖/κ := by
  change max ‖boundedRadialExteriorTail κ hκ g.1‖
    ‖star (boundedRadialExteriorTail κ hκ (star g.2))‖ ≤ _
  apply max_le
  · exact (boundedRadialExteriorTail_norm κ hκ g.1).trans
      (div_le_div_of_nonneg_right (norm_fst_le g) hκ.le)
  · rw [norm_star]
    have h := boundedRadialExteriorTail_norm κ hκ (star g.2)
    rw [norm_star] at h
    exact h.trans (div_le_div_of_nonneg_right (norm_snd_le g) hκ.le)

theorem circularTail_difference (κ : ℝ) (hκ : 0 < κ) (g h : CircularTailSpace) :
    ‖circularTail κ hκ g-circularTail κ hκ h‖ ≤ ‖g-h‖/κ := by
  change max ‖boundedRadialExteriorTail κ hκ g.1-boundedRadialExteriorTail κ hκ h.1‖
    ‖star (boundedRadialExteriorTail κ hκ (star g.2))-
      star (boundedRadialExteriorTail κ hκ (star h.2))‖ ≤ _
  apply max_le
  · exact (boundedRadialExteriorTail_difference κ hκ g.1 h.1).trans
      (div_le_div_of_nonneg_right (norm_fst_le (g-h)) hκ.le)
  · rw [← star_sub,norm_star]
    have hh := boundedRadialExteriorTail_difference κ hκ (star g.2) (star h.2)
    rw [← star_sub,norm_star] at hh
    exact hh.trans (div_le_div_of_nonneg_right (norm_snd_le (g-h)) hκ.le)

noncomputable def circularTailEvaluation (v : CircularTailSpace) (t : ℝ) : (ℂ × ℂ) × (ℂ × ℂ) :=
  (v.1 t,v.2 t)

theorem circularTailEvaluation_continuous (v : CircularTailSpace) :
    Continuous (circularTailEvaluation v) := v.1.continuous.prodMk v.2.continuous

theorem circularTailEvaluation_norm (v : CircularTailSpace) (t : ℝ) :
    ‖circularTailEvaluation v t‖ ≤ ‖v‖ := by
  exact max_le_max (v.1.norm_coe_le_norm t) (v.2.norm_coe_le_norm t)

theorem circularTailEvaluation_sub (v w : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (v-w) t=circularTailEvaluation v t-circularTailEvaluation w t := rfl

theorem circularTail_hasDerivAt (κ : ℝ) (hκ : 0 < κ) (g : CircularTailSpace) (t : ℝ) :
    let v := circularTail κ hκ g
    HasDerivAt (circularTailEvaluation v)
      ((κ • (v.1 t)+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v.1 t).2)+g.1 t),
       (κ • (v.2 t)+(0,Complex.I*(Real.exp (2*t)/2 : ℝ)*(v.2 t).2)+g.2 t)) t := by
  intro v
  have hp := radialExteriorTailIntegral_hasDerivAt κ ‖g.1‖ t hκ g.1
    g.1.continuous g.1.norm_coe_le_norm
  have hm := (radialExteriorTailIntegral_hasDerivAt κ ‖star g.2‖ t hκ (star g.2)
    (star g.2).continuous (star g.2).norm_coe_le_norm).star
  change HasDerivAt (fun s => v.1 s) _ t at hp
  change HasDerivAt (fun s => v.2 s) _ t at hm
  have hs (w y : ℂ × ℂ) (c : ℝ) :
      star (κ • w+(0,-Complex.I*(c : ℂ)*w.2)+star y)=
        κ • star w+(0,Complex.I*(c : ℂ)*(star w).2)+y := by
    simp only [star_add,star_smul,star_trivial,star_star]
    congr 1
    apply Prod.ext <;> simp [Prod.star_def]
  have hm' : HasDerivAt (fun s => v.2 s)
      (κ • (v.2 t)+(0,Complex.I*(Real.exp (2*t)/2 : ℝ)*(v.2 t).2)+g.2 t) t :=
    hm.congr_deriv (hs _ _ _)
  exact hp.prodMk hm'

end DefocusingNLS

end OAI
