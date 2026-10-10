import OAI.Analysis.LienardCycles.GlobalFit

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArchSymmetries
open ScalarArcs
lemma IsArch.affineOn {φ ψ u : ℝ → ℝ} {h t a b c H C : ℝ}
    (hu : IsArch φ u h t a b) (hht : h<t) (hc : 0<c)
    (he : ∀ x ∈ Icc h t, ψ (H+c^2*x)=C+c*φ x) :
    IsArch ψ (fun y => H+c^2*u ((y-C)/c))
      (H+c^2*h) (H+c^2*t) (C+c*a) (C+c*b) := by
  let χ : ℝ → ℝ := fun x => C+c*φ ((x-H)/c^2)
  have hc2 : c^2≠0 := pow_ne_zero 2 hc.ne'
  have hx (x : ℝ) : (H+c^2*x-H)/c^2=x := by field_simp; ring
  have ha := IsArch.affine hu (ψ:=χ) (H:=H) (C:=C) hc (by intro x; dsimp [χ]; rw [hx])
  apply ha.congr_profile (by nlinarith [sq_pos_of_pos hc])
  intro x hx
  have hm : (x-H)/c^2 ∈ Icc h t := by
    constructor
    · exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith [hx.1])
    · exact (div_le_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith [hx.2])
  have hid : H+c^2*((x-H)/c^2)=x := by field_simp; ring
  simpa only [hid] using he ((x-H)/c^2) hm
end QuinticLienard.ArchSymmetries

namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc
omit hloc [FiniteDimensional ℝ P] in
lemma profile_C1 (p : P) : ContDiffOn ℝ 1 (fun x => Φ (p,x)) (Ioi 0) := by
  intro x hx
  exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
lemma midpoint_of_arch {p : P} {h t a b r : ℝ} {u : ℝ → ℝ}
    (hu : IsArch (fun x => Φ (p,x)) u h t a b) (hh : 0<h) (hht : h<t)
    (hr : 0<r) (hw : (b-a)/2=r) :
    midpointAtWidth Φ ((p,h),r)=(b+a)/2-Φ (p,h) := by
  have hc := canonical_of_positive_arch hu (profile_C1 Φ hΦ p) hh hht
  have hwidth : widthFamily Φ ((p,t),h)=r := by
    dsimp [widthFamily,width]
    rw [hc.1,hc.2]
    exact hw
  rw [midpointAtWidth,peak_eq Φ hΦ hloc hr hh hht hwidth]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hc.1,hc.2]

lemma midpoint_quadratic {p : P} {h r d k : ℝ} (hh : 0<h) (hr : 0<r)
    (he : ∀ x, Φ (p,h+x)=Φ (p,h)+d*x+k*x^2/2) :
    midpointAtWidth Φ ((p,h),r)=QuadraticCoordinates.H ((d,k),r) := by
  let T := WidthCoordinates.peakAtWidth PolynomialModel.profile ((((d,k),0),r))
  have hs := WidthCoordinates.peak_spec PolynomialModel.profile PolynomialModel.profile_contDiff
    PolynomialModel.model_local_flow (p:=(d,k)) (h:=0) hr
  have ha := chosen_arch (entire_arch_exists
    (ArchSymmetries.profile_C1 PolynomialModel.profile PolynomialModel.profile_contDiff (d,k)) hs.1)
  have hb := ArchSymmetries.IsArch.affine ha (ψ:=fun x => Φ (p,x)) (H:=h) (C:=Φ (p,h))
    (by norm_num : (0:ℝ)<1) (by intro x; simpa only [one_pow,one_mul,PolynomialModel.profile] using (he x).trans (by ring))
  simp only [one_pow,one_mul,add_zero] at hb
  have hw : ((Φ (p,h)+upper (fun x => PolynomialModel.profile ((d,k),x)) 0 T)-
      (Φ (p,h)+lower (fun x => PolynomialModel.profile ((d,k),x)) 0 T))/2=r := by
    have hh := hs.2
    change (upper (fun x => PolynomialModel.profile ((d,k),x)) 0 T-
      lower (fun x => PolynomialModel.profile ((d,k),x)) 0 T)/2=r at hh
    linarith only [hh]
  have hm := midpoint_of_arch Φ hΦ hloc hb hh (by change h<h+T; linarith [hs.1]) hr hw
  rw [hm]
  dsimp [QuadraticCoordinates.H,WidthCoordinates.midpointAtWidth,WidthCoordinates.midpointFamily,
    ScalarArcs.midpoint,T,PolynomialModel.profile]
  ring
end QuinticLienard.PositiveWidth

end OAI
