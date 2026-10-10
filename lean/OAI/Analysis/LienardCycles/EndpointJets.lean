import OAI.Analysis.LienardCycles.EndpointScaling

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
open PartialCalculus QuadraticCoordinates
noncomputable def Xj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.X1 (m q) (n q) (ell q) (w q)
noncomputable def Xjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.X2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def Zj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.Z1 (m q) (n q) (ell q) (w q)
noncomputable def Zjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.Z2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def gj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.gamma1 (m q) (n q) (ell q) (w q)
noncomputable def gjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.gamma2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def gr := direction ((0,0),1) QuadraticCoordinates.gamma
noncomputable def grr := direction ((0,0),1) gr

lemma endpoint_identities {d k r : ℝ} (hr : 0 < r) :
    EndpointAlgebra.X (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=k*P ((d,k),r)+d ∧
    EndpointAlgebra.Z (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=d*P ((d,k),r)+3*k*Q ((d,k),r) ∧
    EndpointAlgebra.gamma (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=QuadraticCoordinates.gamma ((d,k),r) := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hv := ne_of_gt (mr_pos (d := d) (k := k) hr)
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  dsimp only [m,n] at hm hn
  constructor
  · rw [width_identity hr]
    dsimp [EndpointAlgebra.X,m,n,ell,gap]
    field_simp
    ring
  constructor
  · rw [← euler_identity hr]
    dsimp [EndpointAlgebra.Z,m,n,ell]
    field_simp
    ring
  · dsimp [EndpointAlgebra.gamma,QuadraticCoordinates.gamma,m,n,ell,gap]
    field_simp
    ring

lemma m_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => m ((d,k),s)) (1-Hr ((d,k),r)) r :=
  (hasDerivAt_id r).sub (Hr_hasDerivAt hr)
lemma n_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => n ((d,k),s)) (ell ((d,k),r)*(1-Hr ((d,k),r))) r := by
  convert! (hasDerivAt_id r).add (Hr_hasDerivAt (d := d) (k := k) hr) using 1
  dsimp [ell]
  field_simp [ne_of_gt (mr_pos (d := d) (k := k) hr)]
lemma ell_deriv_scaled {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ell ((d,k),s)) (ell ((d,k),r)*w ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (mr_pos (d := d) (k := k) hr)
  have hp : 1+Hr ((d,k),r) ≠ 0 := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  convert! ell_deriv (d := d) (k := k) hr using 1
  dsimp [ell,w]
  field_simp
lemma w_deriv_scaled {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => w ((d,k),s)) ((sch ((d,k),r)+(1/2)*(w ((d,k),r))^2)*(1-Hr ((d,k),r))) r := by
  simpa only [mul_comm] using w_deriv (d := d) (k := k) hr

lemma endpoint_first_derivs {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => EndpointAlgebra.X (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (Xj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => EndpointAlgebra.Z (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (Zj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => EndpointAlgebra.gamma (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (gj ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hl : 1+ell ((d,k),r) ≠ 0 := by have := ell_pos (d := d) (k := k) hr; positivity
  exact ⟨EndpointAlgebra.X_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hm hn hl,
    EndpointAlgebra.Z_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hl,
    EndpointAlgebra.gamma_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hm hn hl⟩

lemma endpoint_second_derivs {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Xj ((d,k),s)) (Xjj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => Zj ((d,k),s)) (Zjj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => gj ((d,k),s)) (gjj ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hl : 1+ell ((d,k),r) ≠ 0 := by have := ell_pos (d := d) (k := k) hr; positivity
  exact ⟨EndpointAlgebra.X1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hm hn hl,
    EndpointAlgebra.Z1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hl,
    EndpointAlgebra.gamma1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hm hn hl⟩

lemma gamma_analytic {d k r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω QuadraticCoordinates.gamma ((d,k),r) := by
  unfold QuadraticCoordinates.gamma gap
  have hH := H_analytic (d := d) (k := k) hr
  have hHr := Hr_analytic (d := d) (k := k) hr
  fun_prop (disch := exact pow_ne_zero _ (ne_of_gt (H_gap_pos hr)))
lemma gr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω gr ((d,k),r) :=
  direction_contDiffAt (gamma_analytic hr) _
lemma gr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => QuadraticCoordinates.gamma ((d,k),s)) (gr ((d,k),r)) r :=
  slice_r ((gamma_analytic hr).differentiableAt (by simp))
lemma grr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => gr ((d,k),s)) (grr ((d,k),r)) r :=
  slice_r ((gr_analytic hr).differentiableAt (by simp))

lemma first_jets {d k r : ℝ} (hr : 0 < r) :
    Xj ((d,k),r)*(1-Hr ((d,k),r))=k*R ((d,k),r) ∧
    Zj ((d,k),r)*(1-Hr ((d,k),r))=d*R ((d,k),r)+3*k*S ((d,k),r) ∧
    gj ((d,k),r)*(1-Hr ((d,k),r))=gr ((d,k),r) := by
  have he : ∀ᶠ s in 𝓝 r, 0 < s := eventually_gt_nhds hr
  have h1 := (endpoint_first_derivs (d := d) (k := k) hr).1
  have h2 := (endpoint_first_derivs (d := d) (k := k) hr).2.1
  have h3 := (endpoint_first_derivs (d := d) (k := k) hr).2.2
  constructor
  · have ht := (((R_hasDerivAt (d := d) (k := k) hr).const_mul k).add_const d).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).1))
    exact h1.unique ht
  constructor
  · have ht := (((R_hasDerivAt (d := d) (k := k) hr).const_mul d).add
      ((S_hasDerivAt (d := d) (k := k) hr).const_mul (3*k))).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).2.1))
    exact h2.unique ht
  · exact h3.unique ((gr_deriv (d := d) (k := k) hr).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).2.2)))

lemma second_jets {d k r : ℝ} (hr : 0 < r) :
    Xjj ((d,k),r)*(1-Hr ((d,k),r))^2-Xj ((d,k),r)*Hrr ((d,k),r)=k*Rr ((d,k),r) ∧
    Zjj ((d,k),r)*(1-Hr ((d,k),r))^2-Zj ((d,k),r)*Hrr ((d,k),r)=d*Rr ((d,k),r)+3*k*Sr ((d,k),r) ∧
    gjj ((d,k),r)*(1-Hr ((d,k),r))^2-gj ((d,k),r)*Hrr ((d,k),r)=grr ((d,k),r) := by
  have he : ∀ᶠ s in 𝓝 r, 0 < s := eventually_gt_nhds hr
  have hm := (Hrr_hasDerivAt (d := d) (k := k) hr).const_sub 1
  have h1 := ((endpoint_second_derivs (d := d) (k := k) hr).1.mul hm).unique
    (((Rr_hasDerivAt (d := d) (k := k) hr).const_mul k).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).1)))
  have h2 := ((endpoint_second_derivs (d := d) (k := k) hr).2.1.mul hm).unique
    ((((Rr_hasDerivAt (d := d) (k := k) hr).const_mul d).add
      ((Sr_hasDerivAt (d := d) (k := k) hr).const_mul (3*k))).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).2.1)))
  have h3 := ((endpoint_second_derivs (d := d) (k := k) hr).2.2.mul hm).unique
    ((grr_deriv (d := d) (k := k) hr).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).2.2)))
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  · nlinarith only [h3]

lemma Xj_pos {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) : 0 < Xj ((d,k),r) := by
  have h := (first_jets (d := d) (k := k) hr).1
  exact pos_of_mul_pos_left (h.symm ▸ mul_pos hk (R_pos hr)) (mr_pos hr).le

lemma determinant_W {d k r : ℝ} (hr : 0 < r) :
    (Xj ((d,k),r)*Zjj ((d,k),r)-Zj ((d,k),r)*Xjj ((d,k),r))*(1-Hr ((d,k),r))^3=
      3*k^2*W ((d,k),r) := by
  obtain ⟨hx,hz,_⟩ := first_jets (d := d) (k := k) hr
  obtain ⟨hxx,hzz,_⟩ := second_jets (d := d) (k := k) hr
  dsimp only [W]
  linear_combination (Zjj ((d,k),r)*(1-Hr ((d,k),r))^2-Hrr ((d,k),r)*Zj ((d,k),r))*hx +
    (-Xjj ((d,k),r)*(1-Hr ((d,k),r))^2+Hrr ((d,k),r)*Xj ((d,k),r))*hz +
    k*R ((d,k),r)*hzz-(d*R ((d,k),r)+3*k*S ((d,k),r))*hxx
end QuinticLienard.ModelEndpoint

end OAI
