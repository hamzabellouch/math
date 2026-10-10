import OAI.Analysis.LienardCycles.ArchSymmetries

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs CanonicalVariation ArchSymmetries PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

noncomputable def H (q : (ℝ × ℝ) × ℝ) : ℝ := midpointAtWidth profile ((q.1,0),q.2)
noncomputable def P : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) H
noncomputable def Q : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) H
noncomputable def Hr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) H
noncomputable def R : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) P
noncomputable def S : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) Q
noncomputable def G (q : (ℝ × ℝ) × ℝ) : ℝ := P q*S q-Q q*R q

lemma H_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω H ((d,k),r) :=
  (midpointAtWidth_analytic profile profile_contDiff model_local_flow hr).comp ((d,k),r)
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)

lemma P_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω P ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma Q_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Q ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma Hr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Hr ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma R_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω R ((d,k),r) :=
  direction_contDiffAt (P_analytic hr) _
lemma S_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω S ((d,k),r) :=
  direction_contDiffAt (Q_analytic hr) _

lemma P_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((s,k),r)) (P ((d,k),r)) d := by
  simpa [P,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt d
      (((hasDerivAt_id d).prodMk (hasDerivAt_const d k)).prodMk (hasDerivAt_const d r))
lemma Q_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((d,s),r)) (Q ((d,k),r)) k := by
  simpa [Q,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k
      (((hasDerivAt_const k d).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
lemma Hr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((d,k),s)) (Hr ((d,k),r)) r := by
  simpa [Hr,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma Hr_abs_lt {d k r : ℝ} (hr : 0 < r) : |Hr ((d,k),r)| < 1 := by
  rw [←(Hr_hasDerivAt (d := d) (k := k) hr).deriv]
  exact midpoint_width_deriv_abs_lt profile profile_contDiff model_local_flow hr

lemma H_abs_lt {d k r : ℝ} (hr : 0 < r) : |H ((d,k),r)| < r :=
  midpointAtWidth_abs_lt profile profile_contDiff model_local_flow hr

lemma H_gap_pos {d k r : ℝ} (hr : 0 < r) : 0 < r^2-(H ((d,k),r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using H_abs_lt (d := d) (k := k) hr))

lemma translation (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    M profile (d,k) (h,r) = H ((d+k*h,k),r) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (d+k*h,k)) (q := (d,k)) (h := 0) (H := h)
    (C := d*h+k/2*h^2) hr (show 0 < (1:ℝ) by norm_num)
    (by intro x; dsimp [profile]; ring)).2
  simpa [M,H] using hh

lemma scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    H ((d,k),r) = r*H ((d*r,k*r^3),1) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (d*r,k*r^3)) (q := (d,k)) (h := 0) (H := 0) (C := 0)
    (show 0 < (1:ℝ) by norm_num) hr (by intro x; dsimp [profile]; ring)).2
  simpa [H] using hh

lemma reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    H ((-d,-k),r) = -H ((d,k),r) := by
  exact (fixed_width_reflect profile profile_contDiff model_local_flow
    (p := (d,k)) (q := (-d,-k)) (h := 0) hr
    (by intro x; dsimp [profile]; ring)).2

lemma parabolic_arch {r : ℝ} (hr : 0 < r) :
    IsArch (fun _ => 0) (fun y => (r^2-y^2)/2) 0 (r^2/2) (-r) r := by
  constructor
  · fun_prop
  · simpa using hr
  · exact hr
  · norm_num
  · ring
  · ring
  · linarith
  · exact hr
  · intro y _
    convert ((hasDerivAt_const y (r^2)).sub ((hasDerivAt_id y).pow 2)).div_const 2 using 1 <;>
      (first | rfl | (dsimp; ring))
  · intro y hy
    have hh : y^2 ≤ r^2 := by nlinarith [mul_nonneg (show 0 ≤ r-y by linarith [hy.2]) (show 0 ≤ r+y by linarith [hy.1])]
    constructor <;> nlinarith [sq_nonneg y]
  · intro y₁ hy₁ y₂ hy₂ hyy
    have hh := mul_pos (sub_pos.mpr hyy) (show 0 < -y₁-y₂ by linarith [hy₂.2])
    dsimp
    nlinarith
  · intro y₁ hy₁ y₂ hy₂ hyy
    have hh := mul_pos (sub_pos.mpr hyy) (show 0 < y₁+y₂ by linarith [hy₁.1])
    dsimp
    nlinarith

lemma zero_data {r : ℝ} (hr : 0 < r) :
    peakAtWidth profile (((0,0),0),r) = r^2/2 ∧ H ((0,0),r) = 0 := by
  have ht : 0 < r^2/2 := div_pos (sq_pos_of_pos hr) (by norm_num)
  have he : (fun x => profile ((0,0),x)) = (fun _ => (0:ℝ)) := by ext; simp [profile]
  have hu := canonical_of_arch (parabolic_arch hr) contDiff_const ht
  have hw : widthFamily profile (((0,0),r^2/2),0) = r := by
    dsimp [widthFamily,width]
    rw [he,hu.1,hu.2]
    ring
  have hp := peak_eq profile profile_contDiff model_local_flow hr ht hw
  refine ⟨hp,?_⟩
  dsimp [H,midpointAtWidth]
  rw [hp]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [he,hu.1,hu.2]
  simp [profile]

end QuinticLienard.QuadraticCoordinates

end OAI
