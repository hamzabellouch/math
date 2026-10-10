import Mathlib
import OAI.Analysis.SymmetricDomains.InfinitesimalGeneratorEquivariant

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
include hU ha

theorem oneParameter_fixed_of_generator_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0) (t : ℝ) :
    (a t).toHomeomorph p=p := by
  have hd (s : ℝ) : HasDerivAt (fun t => ((a t).toHomeomorph p).val) 0 s := by
    have hs := oneParameter_orbit_ODE hU a ha hb hzero hmul p s
    rwa [infinitesimalGenerator_equivariant hU a ha hb hzero hmul p s,hX,map_zero] at hs
  apply Subtype.ext
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [hzero,one_apply] using hc

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include hU ha

theorem derivativeAt_eq_one_of_generator_zero_jet (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0)
    (hdX : fderiv ℂ (infinitesimalGenerator a) p.val=0)
    {r : ℝ} (hr : 0<r) (hu : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val)) :
    (a r).derivativeAt p=1 := by
  have hF := shortTimeAverage_analytic hU a ha hb hr p.val p.property
  have huN : ∀ᶠ y in 𝓝 p.val, IsUnit (fderiv ℂ (shortTimeAverage a r) y) :=
    hF.fderiv.continuousAt (Units.isOpen.mem_nhds hu)
  have hprod := hF.fderiv.differentiableAt.hasFDerivAt.clm_apply
    ((infinitesimalGenerator_analytic hU a ha hb hzero hmul p.val p.property).differentiableAt.hasFDerivAt)
  have he : (fun y => (fderiv ℂ (shortTimeAverage a r) y) (infinitesimalGenerator a y)) =ᶠ[𝓝 p.val]
      (fun y => r⁻¹ • ((a r).ambientAut y-y)) := by
    filter_upwards [huN,hU.mem_nhds p.property] with y hy hyU
    rw [infinitesimalGenerator_formula hU a ha hb hzero hmul hr hyU hy]
    change ((fderiv ℂ (shortTimeAverage a r) y * Ring.inverse (fderiv ℂ (shortTimeAverage a r) y))
      (r⁻¹ • ((a r).ambientAut y-y))) = _
    rw [Ring.mul_inverse_cancel _ hy,one_apply_eq_self]
  have hprod0 : HasFDerivAt (fun y => r⁻¹ • ((a r).ambientAut y-y)) (0 : Affine n →L[ℂ] Affine n) p.val := by
    have hd := hprod.congr_of_eventuallyEq (he.mono (fun _ h => h.symm))
    simpa only [hX,hdX,ContinuousLinearMap.comp_zero,map_zero,add_zero] using hd
  have hV : HasFDerivAt (fun y => r⁻¹ • ((a r).ambientAut y-y))
      (r⁻¹ • ((a r).derivativeAt p-1)) p.val := by
    have hd := (((a r).ambientAut_analytic hU p.val p.property).differentiableAt.hasFDerivAt.sub
      (hasFDerivAt_id p.val)).const_smul r⁻¹
    convert! hd using 1
  have hz := hV.unique hprod0
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (inv_ne_zero hr.ne'))

theorem oneParameter_eq_one_of_generator_zero_jet
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0)
    (hdX : fderiv ℂ (infinitesimalGenerator a) p.val=0) (t : ℝ) :
    a t=1 := by
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0,
      IsUnit (r⁻¹ • ∫ s in 0..r, (a s).derivativeAt p) :=
    (shortTimeAverage_linear_tendsto hU a ha hzero p).eventually (Units.isOpen.mem_nhds isUnit_one)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0<r := self_mem_nhdsWithin
  have hid : ∀ᶠ r : ℝ in 𝓝[>] 0, a r=1 := by
    filter_upwards [hpos,hu] with r hr hur
    have hunit : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val) := by
      rwa [(shortTimeAverage_derivative hU a ha hb hr p.property).fderiv]
    exact eq_one_of_firstJet hU hc hb (a r) p
      (oneParameter_fixed_of_generator_zero hU a ha hb hzero hmul p hX r)
      (derivativeAt_eq_one_of_generator_zero_jet hU a ha hb hzero hmul p hX hdX hr hunit)
  have hXall (q : U) : infinitesimalGenerator a q.val=0 := by
    have ht := (oneParameter_hasDerivAt_zero hU a ha hb hzero hmul q).tendsto_slope_zero_right
    have he : (fun r : ℝ => r⁻¹ • (((a (0+r)).toHomeomorph q).val-((a 0).toHomeomorph q).val)) =ᶠ[𝓝[>] 0]
        (fun _ => (0 : Affine n)) := by
      filter_upwards [hid] with r hr
      simp only [zero_add,hr,hzero,one_apply,sub_self,smul_zero]
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))
  apply ext
  intro q
  simpa only [one_apply] using oneParameter_fixed_of_generator_zero hU a ha hb hzero hmul q (hXall q) t

end Biholomorph
end Release061

end

end OAI
