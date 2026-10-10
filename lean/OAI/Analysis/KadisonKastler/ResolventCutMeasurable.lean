import OAI.Analysis.KadisonKastler.ResolventCutOrder
import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! # Measurability of resolvent cuts

Monotone projection norms make the diagonal coefficients measurable.
Polarization and the countable Hilbert coefficient criterion then give the
strong measurability needed for the regular-core field construction.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventLowerCut_diagonal (R : H →L[ℂ] H) (r : ℝ) (x : H) :
    inner ℂ (resolventLowerCut R r x) x = (‖resolventLowerCut R r x‖ : ℂ) ^ 2 := by
  let K := (resolventCutGenerator R r).range.topologicalClosure
  have hp : K.starProjection (K.starProjection x) = K.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  have hi := K.inner_starProjection_left_eq_right (K.starProjection x) x
  rw [hp] at hi
  exact hi.trans (inner_self_eq_norm_sq_to_K _)

theorem resolventLowerCut_diagonal_measurable (R : H →L[ℂ] H) (x : H) :
    Measurable (fun r : ℝ => inner ℂ (resolventLowerCut R r x) x) := by
  have hm := (resolventLowerCut_norm_mono R x).measurable
  have hc : Measurable (fun r : ℝ => (‖resolventLowerCut R r x‖ : ℂ) ^ 2) :=
    (Complex.continuous_ofReal.measurable.comp hm).pow_const 2
  simpa only [resolventLowerCut_diagonal] using hc

theorem resolventLowerCut_coefficient_measurable (R : H →L[ℂ] H) (x y : H) :
    Measurable (fun r : ℝ => inner ℂ x (resolventLowerCut R r y)) := by
  have hm : Measurable (fun r : ℝ => inner ℂ (resolventLowerCut R r y) x) := by
    have ha := resolventLowerCut_diagonal_measurable R (x + y)
    have hb := resolventLowerCut_diagonal_measurable R (x - y)
    have hc := resolventLowerCut_diagonal_measurable R (x + Complex.I • y)
    have hd := resolventLowerCut_diagonal_measurable R (x - Complex.I • y)
    have hI : Measurable (fun _ : ℝ => Complex.I) := measurable_const
    have h := ((ha.sub hb).add (hI.mul hc)).sub (hI.mul hd)
    have h' := h.div_const (4 : ℂ)
    convert h' using 1
    funext r
    exact inner_map_polarization (resolventLowerCut R r).toLinearMap x y
  simpa only [Function.comp_def, inner_conj_symm] using
    Complex.continuous_conj.measurable.comp hm

variable [TopologicalSpace.SeparableSpace H]

theorem resolventLowerCut_comp_aestronglyMeasurable (R : H →L[ℂ] H)
    (f : ℝ → ℝ) (hf : Measurable f) (x : H) :
    AEStronglyMeasurable (fun t : ℝ => resolventLowerCut R (f t) x) volume := by
  apply aestronglyMeasurable_of_inner
  intro y
  exact ((resolventLowerCut_coefficient_measurable R y x).comp hf).aestronglyMeasurable

theorem modularUpperCut_measurable {M : VonNeumannAlgebra H}
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun ξ : ℝ => modularUpperCut M J Ω (a - 2 * Real.pi * ξ) x)
      volume := by
  apply resolventLowerCut_comp_aestronglyMeasurable
  exact (show Continuous (fun ξ : ℝ => modularCutThreshold (a - 2 * Real.pi * ξ)) by
    unfold modularCutThreshold
    apply Continuous.inv₀ (by fun_prop)
    intro ξ
    positivity).measurable

end

end KadisonKastler

end OAI
