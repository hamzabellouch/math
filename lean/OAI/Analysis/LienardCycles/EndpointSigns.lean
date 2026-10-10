import OAI.Analysis.LienardCycles.SchwarzianScaling

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

lemma sch_eq {d k r : ℝ} : sch ((d,k),r)=
    ModelAlgebra.schwarzian (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r)) (k/2) d := by
  dsimp [sch,ModelAlgebra.schwarzian]
  ring

lemma actual_zero_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hZero : ModelAlgebra.dStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
      (w ((d,k),r)) (sch ((d,k),r))=0) :
    m ((d,k),r) ≠ n ((d,k),r) ∧
      0 < (ModelAlgebra.wStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))-w ((d,k),r))/
        (m ((d,k),r)-n ((d,k),r)) := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  apply ModelAlgebra.zero_sign_unscaled hm hn hl (show 0 < k/2 by linarith)
  · intro hmn
    have hH : 0 ≤ H ((d,k),r) := by dsimp [m,n] at hmn; linarith
    have hHr := Hr_pos_of_H_nonneg hk hr hH
    refine ⟨?_,w_pos_of_H_nonneg hk hr hH⟩
    exact (lt_div_iff₀ (mr_pos hr)).mpr (by linarith)
  · intro hnm
    apply d_neg_of_H_neg hk hr
    dsimp [m,n] at hnm
    linarith
  · intro hnm hl1
    have hH : H ((d,k),r) < 0 := by dsimp [m,n] at hnm; linarith
    have hHr : 0 ≤ Hr ((d,k),r) := by
      have hh := (le_div_iff₀ (mr_pos (d := d) (k := k) hr)).mp hl1
      linarith
    exact w_nonneg_of_H_neg_Hr_nonneg hk hr hH hHr
  · change d < EndpointAlgebra.X (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
    rw [(endpoint_identities hr).1]
    have hh := mul_pos hk (QuadraticVariation.P_pos (d := d) (k := k) hr)
    linarith
  · intro hnm hdisc
    have hH : H ((d,k),r) < 0 := by dsimp [m,n] at hnm; linarith
    have hd := d_neg_of_H_neg hk hr hH
    obtain ⟨c⟩ := lower_chart (d := d) (k := k) hr
    have hh := c.variation_bound hr hk hd (Real.sqrt_nonneg (d^2/4-(k/2)*m ((d,k),r)))
      (Real.sq_sqrt (show 0 ≤ d^2/4-(k/2)*m ((d,k),r) by linarith))
    rwa [c.log_deriv hr] at hh
  · rwa [← sch_eq]

lemma dStar_zero_of_W_zero {d k r : ℝ} (hr : 0 < r) (hW : W ((d,k),r)=0) :
    ModelAlgebra.dStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
      (w ((d,k),r)) (sch ((d,k),r))=0 := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  have hln : 1+ell ((d,k),r) ≠ 0 := by positivity
  have hh := determinant_W (d := d) (k := k) hr
  rw [hW,mul_zero] at hh
  have hd : Xj ((d,k),r)*Zjj ((d,k),r)-Zj ((d,k),r)*Xjj ((d,k),r)=0 :=
    (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ (ne_of_gt (mr_pos hr)))
  rw [Xj,Xjj,Zj,Zjj,EndpointAlgebra.determinant (ne_of_gt hm) (ne_of_gt hn) hln] at hd
  exact (mul_eq_zero.mp hd).resolve_left (ne_of_gt (by positivity))

lemma gamma_zero_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) (hW : W ((d,k),r)=0) :
    0 < gjj ((d,k),r)-Xjj ((d,k),r)/Xj ((d,k),r)*gj ((d,k),r) := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  have hln : 1+ell ((d,k),r) ≠ 0 := by positivity
  have hmn : m ((d,k),r)+n ((d,k),r) ≠ 0 := ne_of_gt (add_pos hm hn)
  have hd := dStar_zero_of_W_zero hr hW
  obtain ⟨hne,hpos⟩ := actual_zero_sign hk hr hd
  have hf := EndpointAlgebra.gamma_factor (ne_of_gt hm) (ne_of_gt hn) hln hmn hne
    (ne_of_gt (Xj_pos hk hr)) hd
  change 0 < EndpointAlgebra.gamma2 _ _ _ _ _ - EndpointAlgebra.X2 _ _ _ _ _ /
    EndpointAlgebra.X1 _ _ _ _ * EndpointAlgebra.gamma1 _ _ _ _
  rw [hf, mul_div_assoc]
  exact mul_pos (by positivity) hpos

lemma gamma_source_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) (hW : W ((d,k),r)=0) :
    0 < grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r) := by
  have ha := mr_pos (d := d) (k := k) hr
  have hR := R_pos (d := d) (k := k) hr
  have hX := Xj_pos (d := d) hk hr
  obtain ⟨hx,_,hg⟩ := first_jets (d := d) (k := k) hr
  obtain ⟨hxx,_,hgg⟩ := second_jets (d := d) (k := k) hr
  have heq : grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r)=
      (1-Hr ((d,k),r))^2*(gjj ((d,k),r)-Xjj ((d,k),r)/Xj ((d,k),r)*gj ((d,k),r)) := by
    apply (mul_right_inj' (ne_of_gt (mul_pos hR hX))).mp
    field_simp
    linear_combination -R ((d,k),r)*Xj ((d,k),r)*hgg +
      Xj ((d,k),r)*Rr ((d,k),r)*hg +
      gj ((d,k),r)*R ((d,k),r)*hxx -
      gj ((d,k),r)*Rr ((d,k),r)*hx
  rw [heq]
  exact mul_pos (sq_pos_of_pos ha) (gamma_zero_sign hk hr hW)
end QuinticLienard.ModelEndpoint

end OAI
