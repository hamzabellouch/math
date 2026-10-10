import OAI.Probability.SLE.Stochastic.PlanarHolomorphicTests
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

/-! The bounded angular harmonic functions for the two sides of the
real boundary, together with their one-sided boundary limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def halfPlaneExitWeight (positive : Bool) (z : ℂ) : ℝ :=
  if positive then 1-z.arg/Real.pi else z.arg/Real.pi

lemma halfPlaneExitWeight_bounds (s : Bool) {z : ℂ} (hz : 0 < z.im) :
    halfPlaneExitWeight s z∈Icc (0:ℝ) 1 := by
  have h0 : 0 ≤ z.arg/Real.pi := div_nonneg (Complex.arg_nonneg_iff.mpr hz.le) Real.pi_pos.le
  have h1 : z.arg/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (Complex.arg_le_pi z)
  cases s <;> simp only [halfPlaneExitWeight,Bool.false_eq_true,↓reduceIte,mem_Icc] <;>
    constructor <;> linarith

lemma halfPlaneExitWeight_planar (s : Bool) {D : Set ℂ} (hD : IsOpen D)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g D) (hgH : MapsTo g D upperHalfPlane) (w : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => halfPlaneExitWeight s (g (w+Complex.equivRealProdCLM.symm z))) (planarTranslatedDomain D w) ∧
    ∀ z∈planarTranslatedDomain D w,
      planarGenerator (fun z => halfPlaneExitWeight s (g (w+Complex.equivRealProdCLM.symm z))) z=0 := by
  have hlog : DifferentiableOn ℂ Complex.log upperHalfPlane := by
    intro z hz
    exact (Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz)))).differentiableWithinAt
  let Q (z : ℂ) := Complex.log (g z)/(Real.pi:ℂ)
  have hQ : DifferentiableOn ℂ Q D := (hlog.comp hg hgH).div_const _
  cases s
  · have hh := (holomorphic_planar_components hD hQ w).2
    simpa only [halfPlaneExitWeight,Bool.false_eq_true,↓reduceIte,Q,Complex.div_ofReal_im,Complex.log_im] using hh
  · have hQc : DifferentiableOn ℂ (fun z => Complex.I-Q z) D := (differentiableOn_const Complex.I).sub hQ
    have hh := (holomorphic_planar_components hD hQc w).2
    simpa only [halfPlaneExitWeight,↓reduceIte,Q,Complex.sub_im,Complex.I_im,
      Complex.div_ofReal_im,Complex.log_im] using hh

lemma halfPlaneExitWeight_negative_limit {A : Type*} {l : Filter A}
    {ζ : A → ℂ} {x : ℝ} (hx : x<0) (hζ : ∀ᶠ t in l, 0 ≤ (ζ t).im)
    (hlim : Tendsto ζ l (𝓝 (x:ℂ))) :
    Tendsto (fun t => halfPlaneExitWeight false (ζ t)) l (𝓝 1) := by
  have hh := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (x:ℂ)) (by simpa using hx) (by simp)).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim,hζ⟩)
  simpa only [halfPlaneExitWeight,Bool.false_eq_true,↓reduceIte,Function.comp_apply,
    div_self Real.pi_ne_zero] using hh.div_const Real.pi

lemma halfPlaneExitWeight_positive_limit {A : Type*} {l : Filter A}
    {ζ : A → ℂ} {x : ℝ} (hx : 0<x) (hlim : Tendsto ζ l (𝓝 (x:ℂ))) :
    Tendsto (fun t => halfPlaneExitWeight true (ζ t)) l (𝓝 1) := by
  have hh := (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr
    (Or.inl (by simpa using hx)))).tendsto.comp hlim
  have hq := hh.div_const Real.pi
  simpa only [halfPlaneExitWeight,↓reduceIte,Function.comp_apply,
    Complex.arg_ofReal_of_nonneg hx.le,zero_div,sub_zero] using tendsto_const_nhds.sub hq

end SLEExactGauge

end

end OAI
