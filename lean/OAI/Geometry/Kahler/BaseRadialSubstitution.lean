import OAI.Geometry.Kahler.BaseLogPhase

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hopf_law : Measure.map hopf ((volume : Measure unitInterval).prod torusMeasure) = sigma := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) hopf_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_prod (fun x => f (hopf x)) (compact_continuous_integrable (f.continuous.comp hopf_continuous))]
  exact (hopf_integral f.toContinuousMap).symm

lemma hopf_integral_complex {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ ξ, f ξ ∂sigma) = ∫ u : unitInterval, ∫ z, f (hopf (u,z)) ∂torusMeasure := by
  rw [← hopf_law,integral_map hopf_continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ (compact_continuous_integrable (hf.comp hopf_continuous))

lemma weight_profile_integral {f b : ℝ → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) {R : ℝ} (hR : 0 ≤ R)
    (hzero : b 0=0) (htail : b R=0) (v : ℝ) :
    (∫ y in 0..R, Real.exp (-v*y)*(f y+(1-v)*b y)) = 0 := by
  have hd : ∀ y, HasDerivAt (fun y => Real.exp (-v*y)*b y)
      (Real.exp (-v*y)*(f y+(1-v)*b y)) y := by
    intro y
    have hh := (((hasDerivAt_id y).const_mul (-v)).exp).mul (hode y)
    convert! hh using 1; dsimp [id]; ring
  have hc : Continuous (fun y => Real.exp (-v*y)*(f y+(1-v)*b y)) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y) (hc.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_of_le hR] at hh ⊢
  simpa [hzero,htail] using hh

lemma log_radial_substitution {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) =
      (2/k:ℝ) • ∫ y in 0..R, F y := by
  let g : ℝ → ℂ := fun t => (t⁻¹:ℝ) • F (-k/2*Real.log t)
  let e : ℝ → ℝ := fun y => Real.exp (-2*y/k)
  let e' : ℝ → ℝ := fun y => (-2/k)*Real.exp (-2*y/k)
  have he : ∀ y ∈ uIcc 0 R, HasDerivAt e (e' y) y := by
    rw [uIcc_of_le hR.le]
    intro y hy
    convert! (((hasDerivAt_id y).const_mul (-2)).div_const k).exp using 1; dsimp [e,e']; ring
  have he' : ContinuousOn e' (uIcc 0 R) := by unfold e'; fun_prop
  have heg : ContinuousOn g (e '' uIcc 0 R) := by
    intro t ht
    obtain ⟨y,hy,rfl⟩ := ht
    have hp : 0 < e y := Real.exp_pos _
    exact ((continuousAt_id.inv₀ hp.ne').smul
      (hF.continuousAt.comp ((continuousAt_const.mul (Real.continuousAt_log hp.ne'))))).continuousWithinAt
  have hs := intervalIntegral.integral_deriv_smul_comp' he he' heg
  have hcomp : ∀ y, e' y • g (e y) = (-2/k:ℝ) • F y := by
    intro y
    change ((-2/k)*Real.exp (-2*y/k):ℝ) •
      ((Real.exp (-2*y/k))⁻¹:ℝ) • F (-k/2*Real.log (Real.exp (-2*y/k))) = _
    rw [smul_smul,Real.log_exp]
    have hh : -k/2*(-2*y/k)=y := by field_simp
    rw [hh]
    congr 1
    field_simp
  change (∫ y in 0..R, e' y • g (e y)) = _ at hs
  simp_rw [hcomp] at hs
  rw [intervalIntegral.integral_smul] at hs
  have he0 : e 0=1 := by simp [e]
  have heR : e R=Real.exp (-2*R/k) := rfl
  rw [he0,heR] at hs
  conv_rhs at hs => rw [intervalIntegral.integral_symm]
  change _ = -(∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) at hs
  have hh := congrArg Neg.neg hs
  simpa only [neg_neg,← neg_smul,neg_div,neg_neg] using hh.symm

end PinchedHartogs.BaseConstruction

end

end OAI
