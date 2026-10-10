import OAI.Analysis.LienardCycles.CurvatureJets

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
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus ModelEndpoint

lemma transport_W_at_zero {d k r : ℝ} (hr : 0 < r) (hW : W ((d,k),r)=0) :
    transport W ((d,k),r) = -G ((d,k),r)*(grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r)) := by
  have hR := ne_of_gt (R_pos (d := d) (k := k) hr)
  rw [transport_W hr,hW,mul_zero,zero_add]
  dsimp only [W] at hW
  dsimp only [G]
  field_simp
  linear_combination gr ((d,k),r)*P ((d,k),r)*hW

lemma characteristic_deriv {f : (ℝ × ℝ) × ℝ → ℝ} {z k r : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ ω f ((ReferenceCharacteristic.J ((z,k),r),k),r)) :
    HasDerivAt (fun s => f ((ReferenceCharacteristic.J ((z,k),s),k),s))
      (-transport f ((ReferenceCharacteristic.J ((z,k),r),k),r)/
        alpha ((ReferenceCharacteristic.J ((z,k),r),k),r)) r := by
  have hd := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (f := fun s => ((ReferenceCharacteristic.J ((z,k),s),k),s)) r
    (((ReferenceCharacteristic.J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hd
  convert! hd using 1
  have hg := ne_of_gt (H_gap_pos (d := ReferenceCharacteristic.J ((z,k),r)) (k := k) hr)
  dsimp [transport,alpha,ReferenceCharacteristic.A,gap]
  field_simp [ne_of_gt hr,hg]
  ring

lemma W_pos_of_curvature_pos {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) : 0 < W ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧
      0 < W ((ReferenceCharacteristic.J ((z,k),s),k),s) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left,
      (ReferenceCharacteristic.model_tendsto z k).eventually (W_positive_near_zero z k)] with s hs hsr hW
    exact ⟨hs,hsr,hW hs⟩
  obtain ⟨a,ha,har,hWa⟩ := he.exists
  have hd (s : ℝ) (hs : s ∈ Icc a r) :=
    characteristic_deriv (ha.trans_le hs.1) (W_analytic (d := ReferenceCharacteristic.J ((z,k),s)) (k := k) (ha.trans_le hs.1))
  have hpos := RealAnalysis.positive_of_deriv_pos_at_zero har
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt) hd hWa.le (by
      intro s hs hzero
      have hs0 := ha.trans_le hs.1
      rw [transport_W_at_zero hs0 hzero,neg_mul,neg_neg]
      exact div_pos (mul_pos (G_pos hs0) (gamma_source_sign hk hs0 hzero))
        (div_pos hs0 (H_gap_pos hs0)))
  simpa only [hz] using hpos

lemma P_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : P ((-d,-k),r)=P ((d,k),r) := by
  have h1 := (P_hasDerivAt (d := -d) (k := -k) hr).comp d (hasDerivAt_neg d)
  have h2 := (P_hasDerivAt (d := d) (k := k) hr).neg
  have hh := h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall (fun s => reflection s k hr)))
  linarith
lemma Q_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Q ((-d,-k),r)=Q ((d,k),r) := by
  have h1 := (Q_hasDerivAt (d := -d) (k := -k) hr).comp k (hasDerivAt_neg k)
  have h2 := (Q_hasDerivAt (d := d) (k := k) hr).neg
  have hh := h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall (fun s => reflection d s hr)))
  linarith
lemma R_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : R ((-d,-k),r)=R ((d,k),r) := by
  exact (R_hasDerivAt hr).unique ((R_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => P_reflection d k hs)))
lemma S_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : S ((-d,-k),r)=S ((d,k),r) := by
  exact (S_hasDerivAt hr).unique ((S_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => Q_reflection d k hs)))
lemma Rr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Rr ((-d,-k),r)=Rr ((d,k),r) := by
  exact (Rr_hasDerivAt hr).unique ((Rr_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => R_reflection d k hs)))
lemma Sr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Sr ((-d,-k),r)=Sr ((d,k),r) := by
  exact (Sr_hasDerivAt hr).unique ((Sr_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => S_reflection d k hs)))
lemma W_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : W ((-d,-k),r)=W ((d,k),r) := by
  simp only [W,R_reflection d k hr,S_reflection d k hr,Rr_reflection d k hr,Sr_reflection d k hr]

lemma W_nonneg {d k r : ℝ} (hr : 0 < r) : 0 ≤ W ((d,k),r) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hh := W_pos_of_curvature_pos (d := -d) (neg_pos.mpr hk) hr
    simpa only [W_reflection d k hr] using hh.le
  · have ht : Tendsto (fun a : ℝ => W ((d,a),r)) (𝓝[>] (0:ℝ)) (𝓝 (W ((d,0),r))) :=
      (((W_analytic (d := d) (k := 0) hr).continuousAt).comp (f := fun a : ℝ => ((d,a),r))
        ((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const)).tendsto.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (W_pos_of_curvature_pos (d := d) ha hr).le
  · exact (W_pos_of_curvature_pos hk hr).le

lemma G_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => G ((d,k),s)) (P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r)) r := by
  convert! ((R_hasDerivAt hr).mul (Sr_hasDerivAt hr)).sub
    ((S_hasDerivAt hr).mul (Rr_hasDerivAt hr)) using 1
  ring

theorem model_inequality {d k r : ℝ} (hr : 0 < r) :
    deriv (fun s => R ((d,k),s)/G ((d,k),s)) r ≤ 0 := by
  have hG := G_pos (d := d) (k := k) hr
  have hd := ((Rr_hasDerivAt (d := d) (k := k) hr).div (G_deriv hr) (ne_of_gt hG))
  change deriv ((fun s => R ((d,k),s)) / (fun s => G ((d,k),s))) r ≤ 0
  rw [hd.deriv]
  have he : Rr ((d,k),r)*G ((d,k),r)-R ((d,k),r)*(P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r))=
      -P ((d,k),r)*W ((d,k),r) := by dsimp [G,W]; ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (QuadraticVariation.P_pos hr).le) (W_nonneg hr)) (sq_nonneg _)
end QuinticLienard.QuadraticCoordinates

end OAI
