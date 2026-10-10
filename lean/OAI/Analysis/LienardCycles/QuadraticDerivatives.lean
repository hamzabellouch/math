import OAI.Analysis.LienardCycles.QuadraticZero

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
open PolynomialModel PartialCalculus

lemma R_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => P ((d,k),s)) (R ((d,k),r)) r := by
  simpa [R,direction] using!
    ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma S_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Q ((d,k),s)) (S ((d,k),r)) r := by
  simpa [S,direction] using!
    ((Q_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))

lemma P_scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    P ((d,k),r) = r^2*P ((d*r,k*r^3),1) := by
  have hright := ((P_hasDerivAt (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).comp d
    ((hasDerivAt_id d).mul_const r)).const_mul r
  have he : (fun s => H ((s,k),r)) = (fun s => r*H ((s*r,k*r^3),1)) := by
    ext s
    exact scaling s k hr
  have hu := (P_hasDerivAt (d := d) (k := k) hr).unique (he ▸ hright)
  convert hu using 1; ring

lemma Q_scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Q ((d,k),r) = r^4*Q ((d*r,k*r^3),1) := by
  have hright := ((Q_hasDerivAt (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).comp k
    ((hasDerivAt_id k).mul_const (r^3))).const_mul r
  have he : (fun s => H ((d,s),r)) = (fun s => r*H ((d*r,s*r^3),1)) := by
    ext s
    exact scaling d s hr
  have hu := (Q_hasDerivAt (d := d) (k := k) hr).unique (he ▸ hright)
  convert hu using 1; ring

noncomputable def Rr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) R
noncomputable def Sr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) S
noncomputable def W (q : (ℝ × ℝ) × ℝ) : ℝ := R q*Sr q-S q*Rr q
lemma Rr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => R ((d,k),s)) (Rr ((d,k),r)) r := by
  simpa [Rr,direction] using!
    ((R_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma Sr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => S ((d,k),s)) (Sr ((d,k),r)) r := by
  simpa [Sr,direction] using!
    ((S_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))

noncomputable def PN (q : (ℝ × ℝ) × ℝ) : ℝ := P ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def QN (q : (ℝ × ℝ) × ℝ) : ℝ := Q ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def PNr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) PN
noncomputable def QNr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) QN
noncomputable def PNrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) PNr
noncomputable def QNrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) QNr

lemma PN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PN q := by
  apply (P_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma QN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QN q := by
  apply (Q_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma PNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PNr q := direction_contDiffAt (PN_analytic q) _
lemma QNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QNr q := direction_contDiffAt (QN_analytic q) _
lemma PNrr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PNrr q := direction_contDiffAt (PNr_analytic q) _
lemma QNrr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QNrr q := direction_contDiffAt (QNr_analytic q) _

lemma slice_r {f : (ℝ × ℝ) × ℝ → ℝ} {q : (ℝ × ℝ) × ℝ}
    (hf : DifferentiableAt ℝ f q) :
    HasDerivAt (fun s => f (q.1,s)) (direction ((0,0),1) f q) q.2 := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))

lemma PNr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => PN ((d,k),s)) (PNr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((PN_analytic ((d,k),r)).differentiableAt (by simp))
lemma QNr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => QN ((d,k),s)) (QNr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((QN_analytic ((d,k),r)).differentiableAt (by simp))
lemma PNrr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => PNr ((d,k),s)) (PNrr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((PNr_analytic ((d,k),r)).differentiableAt (by simp))
lemma QNrr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => QNr ((d,k),s)) (QNrr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((QNr_analytic ((d,k),r)).differentiableAt (by simp))

lemma R_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    R ((d,k),r) = 2*r*PN ((d,k),r)+r^2*PNr ((d,k),r) := by
  have hd := ((hasDerivAt_id r).pow 2).mul (PNr_hasDerivAt d k r)
  have he : (fun s => P ((d,k),s)) =ᶠ[𝓝 r] (fun s => s^2*PN ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact P_scaling d k hs
  have hh := (R_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma S_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    S ((d,k),r) = 4*r^3*QN ((d,k),r)+r^4*QNr ((d,k),r) := by
  have hd := ((hasDerivAt_id r).pow 4).mul (QNr_hasDerivAt d k r)
  have he : (fun s => Q ((d,k),s)) =ᶠ[𝓝 r] (fun s => s^4*QN ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact Q_scaling d k hs
  have hh := (S_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma Rr_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Rr ((d,k),r) = 2*PN ((d,k),r)+4*r*PNr ((d,k),r)+r^2*PNrr ((d,k),r) := by
  have hd := (((hasDerivAt_id r).const_mul 2).mul (PNr_hasDerivAt d k r)).add
    (((hasDerivAt_id r).pow 2).mul (PNrr_hasDerivAt d k r))
  have he : (fun s => R ((d,k),s)) =ᶠ[𝓝 r]
      (fun s => 2*s*PN ((d,k),s)+s^2*PNr ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact R_scaled d k hs
  have hh := (Rr_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma Sr_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Sr ((d,k),r) = 12*r^2*QN ((d,k),r)+8*r^3*QNr ((d,k),r)+r^4*QNrr ((d,k),r) := by
  have hd := ((((hasDerivAt_id r).pow 3).const_mul 4).mul (QNr_hasDerivAt d k r)).add
    (((hasDerivAt_id r).pow 4).mul (QNrr_hasDerivAt d k r))
  have he : (fun s => S ((d,k),s)) =ᶠ[𝓝 r]
      (fun s => 4*s^3*QN ((d,k),s)+s^4*QNr ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact S_scaled d k hs
  have hh := (Sr_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

noncomputable def WN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  (2*PN q+q.2*PNr q)*(12*QN q+8*q.2*QNr q+q.2^2*QNrr q)-
  (4*QN q+q.2*QNr q)*(2*PN q+4*q.2*PNr q+q.2^2*PNrr q)

lemma W_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    W ((d,k),r) = r^3*WN ((d,k),r) := by
  dsimp [W]
  rw [R_scaled d k hr,S_scaled d k hr,Rr_scaled d k hr,Sr_scaled d k hr]
  dsimp [WN]
  ring

lemma WN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω WN q := by
  unfold WN
  have hP := PN_analytic q
  have hQ := QN_analytic q
  have hPr := PNr_analytic q
  have hQr := QNr_analytic q
  have hPrr := PNrr_analytic q
  have hQrr := QNrr_analytic q
  fun_prop

lemma WN_zero (d k : ℝ) : WN ((d,k),0) = 16/45 := by
  norm_num [WN,PN,QN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),
    QuadraticVariation.Q_zero (by norm_num : (0:ℝ)<1)]

theorem W_positive_near_zero (d k : ℝ) :
    ∀ᶠ q in 𝓝 ((d,k),(0:ℝ)), 0 < q.2 → 0 < W q := by
  have hp : 0 < WN ((d,k),0) := by rw [WN_zero]; norm_num
  filter_upwards [(WN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hp)] with q hq hr
  rcases q with ⟨⟨d',k'⟩,r⟩
  rw [W_scaled d' k' hr]
  exact mul_pos (pow_pos hr 3) hq

end QuinticLienard.QuadraticCoordinates

end OAI
