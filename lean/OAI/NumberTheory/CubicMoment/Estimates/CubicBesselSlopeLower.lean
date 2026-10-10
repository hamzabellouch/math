import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSymmetricSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Lower estimates on finite intervals for the actual negative slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_slopeProfile_hasDerivAt (z : ℝ) :
    HasDerivAt (fun x : ℝ => (x-1)*Real.exp (-x))
      ((2-z)*Real.exp (-z)) z := by
  have hd : HasDerivAt (fun x : ℝ => -x) (-1) z := by
    convert (hasDerivAt_id z).neg using 1
    funext x; rfl
  have hg : HasDerivAt (fun x : ℝ => x-1) 1 z := by
    convert (hasDerivAt_id z).sub_const 1 using 1
    funext x; rfl
  convert hg.mul hd.exp using 1
  ring

lemma cubic_slopeProfile_antitone :
    AntitoneOn (fun x : ℝ => (x-1)*Real.exp (-x)) (Ici 2) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by fun_prop)
    (fun z _ => (cubic_slopeProfile_hasDerivAt z).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(cubic_slopeProfile_hasDerivAt z).deriv]
  have hz' : 2≤z := (interior_subset hz)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

lemma cubicWhittakerNegativeSlope_lower {v q : ℝ} (hx : 2≤4*Real.pi*v)
    {u : ℝ} (hq : 4*Real.pi*v*Real.cosh u≤q) :
    (q-1)*Real.exp (-q)≤cubicWhittakerNegativeSlope v u := by
  have hx0 : 0≤4*Real.pi*v := by linarith
  have hz : 2≤4*Real.pi*v*Real.cosh u := by
    nlinarith [Real.one_le_cosh u]
  have h := cubic_slopeProfile_antitone hz (hz.trans hq) hq
  have hn : 0≤(4*Real.pi*v*Real.cosh u-1)*Real.exp (-4*Real.pi*v*Real.cosh u) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  change (q-1)*Real.exp (-q)≤
    (4*Real.pi*v*Real.cosh u-1)*Real.exp (-(4*Real.pi*v*Real.cosh u)) at h
  have hn' : 0≤(4*Real.pi*v*Real.cosh u-1)*
      Real.exp (-(4*Real.pi*v*Real.cosh u)) := by simpa only [neg_mul] using hn
  simpa only [cubicWhittakerNegativeSlope,neg_mul] using
    h.trans (le_mul_of_one_le_right hn' (Real.one_le_cosh (u/3)))

lemma cubicWhittakerNegativeSlope_even (v u : ℝ) :
    cubicWhittakerNegativeSlope v (-u)=cubicWhittakerNegativeSlope v u := by
  simp [cubicWhittakerNegativeSlope,Real.cosh_neg,neg_div]

lemma cubicWhittakerNegativeSlope_nonneg {v : ℝ} (hx : 1≤4*Real.pi*v) (u : ℝ) :
    0≤cubicWhittakerNegativeSlope v u := by
  unfold cubicWhittakerNegativeSlope
  have hx0 : 0≤4*Real.pi*v := by linarith
  have hz : 1≤4*Real.pi*v*Real.cosh u := by nlinarith [Real.one_le_cosh u]
  exact mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.cosh_pos _).le

lemma cubicWhittakerNegativeSlope_interval_lower {v a b q : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) (hab : a≤b)
    (hq : ∀ u∈Ioc a b,4*Real.pi*v*Real.cosh u≤q) :
    (b-a)*((q-1)*Real.exp (-q))≤∫ u in Ioc a b,cubicWhittakerNegativeSlope v u := by
  have hi := (cubicWhittakerNegativeSlope_integral hv).1.integrableOn (s:=Ioc a b)
  have h : (∫ _u in Ioc a b,(q-1)*Real.exp (-q))≤
      ∫ u in Ioc a b,cubicWhittakerNegativeSlope v u := by
    apply setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioc])) hi measurableSet_Ioc
    intro u hu
    exact cubicWhittakerNegativeSlope_lower hx (hq u hu)
  simpa only [setIntegral_const,Measure.real,Real.volume_Ioc,smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

end CubicFirstMoment

end

end OAI
