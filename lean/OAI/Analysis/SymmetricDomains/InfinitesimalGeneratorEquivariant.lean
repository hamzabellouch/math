import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterDifferentiableZero

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)

def infinitesimalGenerator (x : Affine n) : Affine n :=
  deriv (fun t => (a t).ambientAut x) 0

include hU ha

theorem infinitesimalGenerator_formula (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t)
    {r : ℝ} (hr : 0<r) {x : Affine n} (hx : x ∈ U)
    (hu : IsUnit (fderiv ℂ (shortTimeAverage a r) x)) :
    infinitesimalGenerator a x = (Ring.inverse (fderiv ℂ (shortTimeAverage a r) x))
      (r⁻¹ • ((a r).ambientAut x-x)) := by
  let e := ContinuousLinearEquiv.unitsEquiv ℂ (Affine n) hu.unit
  have he : (e : Affine n →L[ℂ] Affine n) = fderiv ℂ (shortTimeAverage a r) x := hu.unit_spec
  have hd : HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) x := by
    rw [he]
    exact (shortTimeAverage_analytic hU a ha hb hr x hx).hasStrictFDerivAt
  have ht := oneParameter_hasDerivAt_of_regular_average a ha hzero hmul r ⟨x,hx⟩ e hd
  have hi : Ring.inverse (fderiv ℂ (shortTimeAverage a r) x) = (e.symm : Affine n →L[ℂ] Affine n) := by
    rw [← he,ContinuousLinearMap.ringInverse_equiv,ContinuousLinearMap.inverse_equiv]
  rw [hi]
  unfold infinitesimalGenerator
  simp_rw [ambientAut_apply (a _) ⟨x,hx⟩]
  exact ht.deriv

theorem infinitesimalGenerator_analytic (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) :
    AnalyticOnNhd ℂ (infinitesimalGenerator a) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro x hx
  obtain ⟨r,hr,e,he⟩ := exists_regular_shortTimeAverage hU a ha hb hzero ⟨x,hx⟩
  have hF := shortTimeAverage_analytic hU a ha hb hr x hx
  have hu : IsUnit (fderiv ℂ (shortTimeAverage a r) x) := by
    rw [he.hasFDerivAt.fderiv]
    exact ⟨(ContinuousLinearEquiv.unitsEquiv ℂ (Affine n)).symm e,rfl⟩
  have huN : ∀ᶠ y in 𝓝 x, IsUnit (fderiv ℂ (shortTimeAverage a r) y) :=
    hF.fderiv.continuousAt (Units.isOpen.mem_nhds hu)
  have hInv : AnalyticAt ℂ (fun y => Ring.inverse (fderiv ℂ (shortTimeAverage a r) y)) x := by
    have hi : AnalyticAt ℂ Ring.inverse (fderiv ℂ (shortTimeAverage a r) x) := by
      simpa only [hu.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu.unit)
    exact hi.comp hF.fderiv
  have hG : DifferentiableAt ℂ (fun y => r⁻¹ • ((a r).ambientAut y-y)) x :=
    (((a r).ambientAut_analytic hU x hx).differentiableAt.sub (differentiableAt_id)).const_smul r⁻¹
  have hc := hInv.differentiableAt.clm_apply hG
  apply (hc.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [huN,hU.mem_nhds hx] with y hy hyU
  exact infinitesimalGenerator_formula hU a ha hb hzero hmul hr hyU hy

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include hU ha

theorem oneParameter_hasDerivAt_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val) (infinitesimalGenerator a p.val) 0 := by
  have h := (oneParameter_differentiableAt_zero hU a ha hb hzero hmul p).hasDerivAt
  simpa only [infinitesimalGenerator,ambientAut_apply] using h

theorem oneParameter_orbit_ODE (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) (s : ℝ) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val)
      (infinitesimalGenerator a ((a s).toHomeomorph p).val) s := by
  have h0 := oneParameter_hasDerivAt_zero hU a ha hb hzero hmul ((a s).toHomeomorph p)
  have h1 : HasDerivAt (fun t => ((a t).toHomeomorph ((a s).toHomeomorph p)).val)
      (infinitesimalGenerator a ((a s).toHomeomorph p).val) (s-s) := by simpa using h0
  have he (t : ℝ) : ((a (t-s)).toHomeomorph ((a s).toHomeomorph p)).val = ((a t).toHomeomorph p).val := by
    rw [← mul_apply,← hmul]; simp only [sub_add_cancel]
  simpa only [he] using h1.comp_sub_const s s

theorem infinitesimalGenerator_equivariant (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) (s : ℝ) :
    infinitesimalGenerator a ((a s).toHomeomorph p).val =
      (a s).derivativeAt p (infinitesimalGenerator a p.val) := by
  have h0 := oneParameter_hasDerivAt_zero hU a ha hb hzero hmul p
  have hp : ((a 0).toHomeomorph p).val=p.val := by rw [hzero,one_apply]
  have hd : HasFDerivAt (a s).ambientAut ((a s).derivativeAt p) ((a 0).toHomeomorph p).val := by
    rw [hp]
    exact ((a s).ambientAut_analytic hU p.val p.property).differentiableAt.hasFDerivAt
  have hc := (hd.restrictScalars ℝ).comp_hasDerivAt 0 h0
  have he (t : ℝ) : (a s).ambientAut ((a t).toHomeomorph p).val =
      ((a t).toHomeomorph ((a s).toHomeomorph p)).val := by
    rw [ambientAut_apply,← mul_apply,← hmul,← mul_apply,← hmul,add_comm s t]
  have hcomp : HasDerivAt (fun t => ((a t).toHomeomorph ((a s).toHomeomorph p)).val)
      ((a s).derivativeAt p (infinitesimalGenerator a p.val)) 0 := by
    convert! hc using 1
    simp only [Function.comp_def,he]
  exact (oneParameter_hasDerivAt_zero hU a ha hb hzero hmul ((a s).toHomeomorph p)).unique hcomp

end Biholomorph
end Release061

end

end OAI
