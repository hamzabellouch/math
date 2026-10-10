import OAI.Analysis.LienardCycles.ScalarComparison

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs
lemma IsArch.height_gt_base {φ u : ℝ → ℝ} {h t A B y : ℝ}
    (hu : IsArch φ u h t A B) (hy : y ∈ Ioo A B) : h<u y := by
  by_cases hp : y≤φ t
  · have hh := hu.inc ⟨le_rfl,hu.lower_lt_peak.le⟩ ⟨hy.1.le,hp⟩ hy.1
    simpa only [hu.lower] using hh
  · have hh := hu.dec ⟨(not_le.mp hp).le,hy.2.le⟩ ⟨hu.peak_lt_upper.le,le_rfl⟩ hy.2
    simpa only [hu.upper] using hh
end QuinticLienard.ScalarArcs
namespace QuinticLienard.QuinticFit
open ScalarArcs QuadraticCoordinates

theorem midpoint_gt_quadratic {a : Fin 6 → ℝ} {h r d κ : ℝ} (hh : 0<h) (hr : 0<r)
    (hφ : ∀ u, h<u → QuinticProfile.profile a (0,u)-QuinticProfile.profile a (0,h)>
      d*(u-h)+κ*(u-h)^2/2) : H ((d,κ),r)<M a (h,r) := by
  by_contra! hn
  let φ : ℝ → ℝ := fun u=>QuinticProfile.profile a (0,u)
  let t := PositiveWidth.peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have hs := PositiveWidth.peak_spec (QuinticProfile.profile a) (fun _ ht=>QuinticProfile.analytic a ht)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  let u := archFunction φ h t
  have hu : IsArch φ u h t (lower φ h t) (upper φ h t) :=
    chosen_arch (positive_arch_exists (PositiveWidth.profile_C1 (QuinticProfile.profile a)
      (fun _ ht=>QuinticProfile.analytic a ht) 0) hh hs.1)
  let ψ₀ : ℝ → ℝ := fun x=>PolynomialModel.profile ((d,κ),x)
  let T := WidthCoordinates.peakAtWidth PolynomialModel.profile (((d,κ),0),r)
  have hT := WidthCoordinates.peak_spec PolynomialModel.profile PolynomialModel.profile_contDiff
    PolynomialModel.model_local_flow (p:=(d,κ)) (h:=0) hr
  have hv₀ := chosen_arch (entire_arch_exists
    (ArchSymmetries.profile_C1 PolynomialModel.profile PolynomialModel.profile_contDiff (d,κ)) hT.1)
  let C := φ h+M a (h,r)-H ((d,κ),r)
  let ψ : ℝ → ℝ := fun x=>C+d*(x-h)+κ*(x-h)^2/2
  let v : ℝ → ℝ := fun y=>h+archFunction ψ₀ 0 T (y-C)
  have hv : IsArch ψ v h (h+T) (C+lower ψ₀ 0 T) (C+upper ψ₀ 0 T) := by
    have hv' := ArchSymmetries.IsArch.affine hv₀ (ψ:=ψ) (H:=h) (C:=C)
      (by norm_num : (0:ℝ)<1) (by intro x; dsimp [ψ,PolynomialModel.profile]; ring)
    simpa only [one_pow,one_mul,div_one,add_zero] using hv'
  have hs2 := hs.2
  change (upper φ h t-lower φ h t)/2=r at hs2
  have hT2 := hT.2
  change (upper ψ₀ 0 T-lower ψ₀ 0 T)/2=r at hT2
  have hM : M a (h,r)=(upper φ h t+lower φ h t)/2-φ h := rfl
  have hH : H ((d,κ),r)=(upper ψ₀ 0 T+lower ψ₀ 0 T)/2 := by
    dsimp [H,WidthCoordinates.midpointAtWidth,WidthCoordinates.midpointFamily,ScalarArcs.midpoint,PolynomialModel.profile,T,ψ₀]
    ring
  have hl : C+lower ψ₀ 0 T=lower φ h t := by dsimp [C]; linarith
  have hr' : C+upper ψ₀ 0 T=upper φ h t := by dsimp [C]; linarith
  rw [hl,hr'] at hv
  let E : ℝ → ℝ := fun y=>u y-v y
  let A : ℝ → ℝ := fun y=> -(d+κ/2*(u y+v y-2*h))
  let F : ℝ → ℝ := fun y=>φ (u y)-ψ (u y)
  have hd (y : ℝ) (hy : y ∈ Icc (lower φ h t) (upper φ h t)) :
      HasDerivAt E (-A y*E y+F y) y := by
    convert! (hu.equation y hy).sub (hv.equation y hy) using 1
    dsimp [A,E,F,ψ]
    ring
  have hf (y : ℝ) (hy : y ∈ Ioo (lower φ h t) (upper φ h t)) : 0<F y := by
    have ho := hφ (u y) (hu.height_gt_base hy)
    dsimp [F,ψ,C]
    change _<φ (u y)-φ h at ho
    linarith
  have hc : ContinuousOn A (Icc (lower φ h t) (upper φ h t)) := by
    exact (continuous_const.add (continuous_const.mul ((hu.continuous.add hv.continuous).sub continuous_const))).neg.continuousOn
  have hp := ScalarComparison.linear_pos (E:=E) (hu.lower_lt_peak.trans hu.peak_lt_upper)
    hc hd hf (by simp only [E,hu.lower,hv.lower,sub_self,le_refl])
  dsimp only [E] at hp
  rw [hu.upper,hv.upper,sub_self] at hp
  exact (lt_irrefl 0) hp
end QuinticLienard.QuinticFit

end OAI
