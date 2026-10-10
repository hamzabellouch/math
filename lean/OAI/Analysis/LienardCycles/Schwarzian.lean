import OAI.Analysis.LienardCycles.CharacteristicLimit

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates RiccatiJets

noncomputable def w (q : (ℝ × ℝ) × ℝ) : ℝ :=
  2*Hrr q/((1-Hr q)^2*(1+Hr q))
noncomputable def sch (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.2*(m q+n q*(ell q)^2)+(q.1.1^2/2)*((ell q)^2-1)-
    q.1.1*(1/m q+(ell q)^2/n q)+(3/2)*((ell q)^2/(n q)^2-1/(m q)^2)

lemma Hrr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Hrr ((d,k),r) :=
  direction_contDiffAt (Hr_analytic hr) _
lemma ell_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω ell ((d,k),r) :=
  (contDiffAt_const.add (Hr_analytic hr)).div (contDiffAt_const.sub (Hr_analytic hr))
    (ne_of_gt (mr_pos hr))
lemma w_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω w ((d,k),r) := by
  have h1 : 1+Hr ((d,k),r) ≠ 0 := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  exact (contDiffAt_const.mul (Hrr_analytic hr)).div
    (((contDiffAt_const.sub (Hr_analytic hr)).pow 2).mul
      (contDiffAt_const.add (Hr_analytic hr)))
    (mul_ne_zero (pow_ne_zero _ (ne_of_gt (mr_pos hr))) h1)
lemma ell_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ell ((d,k),s)) (2*Hrr ((d,k),r)/(1-Hr ((d,k),r))^2) r := by
  convert! ((hasDerivAt_const r (1:ℝ)).add (Hrr_hasDerivAt hr)).div
    ((hasDerivAt_const r (1:ℝ)).sub (Hrr_hasDerivAt hr)) (ne_of_gt (mr_pos hr)) using 1
  dsimp
  ring

lemma LowerChart.radius_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), 0 < c.radius s ∧
      HasDerivAt c.radius (1/(1-Hr ((d,k),c.radius s))) s := by
  have hp : ∀ᶠ s in 𝓝 (m ((d,k),r)), 0 < c.radius s :=
    continuousAt_const.eventually_lt c.radius_analytic.continuousAt (by rw [c.radius_base]; exact hr)
  filter_upwards [hp,c.radius_analytic.eventually (by simp),c.radius_relation.eventually_nhds] with s hs ha he
  have hd := (ha.differentiableAt (by simp)).hasDerivAt
  have heder := (((hasDerivAt_id (c.radius s)).sub (Hr_hasDerivAt hs)).comp s hd).unique
    ((hasDerivAt_id s).congr_of_eventuallyEq he)
  have heq : deriv c.radius s=1/(1-Hr ((d,k),c.radius s)) := by
    apply (eq_div_iff (ne_of_gt (mr_pos hs))).mpr
    simpa only [mul_comm] using heder
  exact ⟨hs,by simpa only [heq] using hd⟩

lemma LowerChart.upper_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv c.upper s=ell ((d,k),c.radius s) := by
  filter_upwards [c.radius_deriv_eventually hr] with s hs
  have hd := ((hasDerivAt_id (c.radius s)).add (Hr_hasDerivAt (d := d) (k := k) hs.1)).comp s hs.2
  have hd' : HasDerivAt c.upper (ell ((d,k),c.radius s)) s := by
    convert! hd.congr_of_eventuallyEq (Eventually.of_forall c.upper_def) using 1
    dsimp [ell]
    ring
  exact hd'.deriv

lemma LowerChart.second_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv (deriv c.upper) s=
      2*Hrr ((d,k),c.radius s)/(1-Hr ((d,k),c.radius s))^3 := by
  filter_upwards [c.radius_deriv_eventually hr,(c.upper_deriv_eventually hr).eventually_nhds] with s hs he
  have hd := ((ell_deriv hs.1).comp s hs.2).congr_of_eventuallyEq he
  rw [hd.deriv]
  field_simp

lemma LowerChart.log_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv (deriv c.upper) s/deriv c.upper s=w ((d,k),c.radius s) := by
  filter_upwards [c.radius_deriv_eventually hr,c.upper_deriv_eventually hr,c.second_deriv_eventually hr] with s hs h1 h2
  rw [h1,h2]
  have hn := ne_of_gt (mr_pos (d := d) (k := k) hs.1)
  dsimp [w,ell]
  field_simp

lemma LowerChart.log_deriv {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r)=w ((d,k),r) := by
  have hh := (c.log_deriv_eventually hr).self_of_nhds
  rwa [c.upper_derivative.deriv,c.radius_base] at hh

lemma LowerChart.schwarzian {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    schwarzian c.upper (m ((d,k),r))=sch ((d,k),r) := (c.formulas hr).1

lemma log_deriv_hasDerivAt {Y : ℝ → ℝ} {s : ℝ} (hY : ContDiffAt ℝ ω Y s) (hl : deriv Y s ≠ 0) :
    HasDerivAt (fun t => deriv (deriv Y) t/deriv Y t)
      (schwarzian Y s+(1/2)*(deriv (deriv Y) s/deriv Y s)^2) s := by
  have hd := ((deriv_analytic (deriv_analytic hY)).differentiableAt (by simp)).hasDerivAt.div
    ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt hl
  convert! hd using 1
  dsimp [schwarzian]
  field_simp
  ring

lemma w_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => w ((d,k),s))
      ((1-Hr ((d,k),r))*(sch ((d,k),r)+(1/2)*(w ((d,k),r))^2)) r := by
  obtain ⟨c⟩ := lower_chart (d := d) (k := k) hr
  have hd := slice_r (q := ((d,k),r)) ((w_analytic hr).differentiableAt (by simp))
  have hdρ := c.radius_derivative
  have hd0 : HasDerivAt (fun s => w ((d,k),s)) (direction ((0,0),1) w ((d,k),r)) (c.radius (m ((d,k),r))) := by
    rw [c.radius_base]; exact hd
  have hc := hd0.comp (m ((d,k),r)) hdρ
  have hwρ : HasDerivAt (fun s => w ((d,k),c.radius s))
      (direction ((0,0),1) w ((d,k),r)*(1/(1-Hr ((d,k),r)))) (m ((d,k),r)) := by
    simpa only [c.radius_base] using! hc
  have hl := ne_of_gt (ell_pos (d := d) (k := k) hr)
  have hYl : deriv c.upper (m ((d,k),r)) ≠ 0 := by rwa [c.upper_derivative.deriv]
  have he := hwρ.unique ((log_deriv_hasDerivAt c.upper_analytic hYl).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (c.log_deriv_eventually hr)))
  rw [c.schwarzian hr,c.upper_derivative.deriv,c.log_deriv hr] at he
  have hfinal : direction ((0,0),1) w ((d,k),r)=
      (1-Hr ((d,k),r))*(sch ((d,k),r)+(1/2)*(w ((d,k),r))^2) := by
    have hn := ne_of_gt (mr_pos (d := d) (k := k) hr)
    field_simp at he
    nlinarith only [he]
  simpa only [hfinal] using hd

end QuinticLienard.ModelEndpoint

end OAI
