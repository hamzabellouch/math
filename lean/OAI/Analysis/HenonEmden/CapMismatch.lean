import OAI.Analysis.HenonEmden.InteractionBounds

namespace OAI

section CapMismatch

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents

lemma cap_close_bound {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    (e : sphere (0:Space n) 1) {x y : Space n}
    (hs : 0 < pairGap (x,y)) (hxy : ‖x-y‖ ≤ δ*pairGap (x,y)^(m n)) :
    |weight volume κ e x-weight volume κ e y| ≤
      oscillationConstant (volume : Measure (Space n)) κ*δ*(eta n x+eta n y) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hC := oscillationConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hlen := (close_pair_gaps hδ hδ1 hs hxy).2.2.2
  have hbound {a b : Space n} (hab : ‖a-b‖ ≤ δ*pairGap (a,b)^(m n))
      (hs' : 0 < pairGap (a,b)) (hlen' : ‖a-b‖ ≤ δ*pairGap (a,b)) (hma : pairGap (a,b)=d a) :
      |weight volume κ e a-weight volume κ e b| ≤
        oscillationConstant (volume : Measure (Space n)) κ*δ*(eta n a+eta n b) := by
    rw [hma] at hab hs' hlen'
    have hd : dist a b ≤ d a/2 := by rw [dist_eq_norm]; nlinarith
    have ho := weight_close_oscillation volume hκ hκ1 hs' hd e
    simp only [finrank_euclideanSpace_fin] at ho
    rw [dist_eq_norm] at ho
    have hp : d a^(N n-n-1)*‖a-b‖ ≤ δ*d a^(N n) := by
      calc
        _ ≤ d a^(N n-n-1)*(δ*d a^(m n)) := mul_le_mul_of_nonneg_left hab (pow_nonneg hs'.le _)
        _ = δ*d a^(N n-n-1+m n) := by rw [pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs'.le (d_le_one a) (by unfold N m; omega)) hδ
    exact ho.trans ((by nlinarith [mul_le_mul_of_nonneg_left hp hC] :
      oscillationConstant (volume : Measure (Space n)) κ*d a^(N n-n-1)*‖a-b‖ ≤
        oscillationConstant (volume : Measure (Space n)) κ*δ*d a^(N n)).trans
      (mul_le_mul_of_nonneg_left ((eta_gap_bounds n a).1.trans (le_add_of_nonneg_right (eta_nonneg n b))) (mul_nonneg hC hδ)))
  rcases max_choice (d x) (d y) with hx | hy
  · exact hbound hxy hs hlen hx
  · have hh := hbound (a:=y) (b:=x) (by simpa only [pairGap,max_comm,norm_sub_rev y x] using hxy)
      (by simpa only [pairGap,max_comm] using hs) (by simpa only [pairGap,max_comm,norm_sub_rev y x] using hlen)
      (by simpa only [pairGap,max_comm] using hy)
    simpa only [abs_sub_comm,add_comm] using hh

lemma cap_endpoint_far_bound {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:Space n) 1) (x y : Space n)
    (hfar : 0 < d x → δ*d x^(m n) ≤ ‖x-y‖) :
    weight volume κ e x ≤ boundConstant (volume : Measure (Space n)) κ*farWeight δ (N n-n:ℕ) (x,y) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  by_cases hx : 0 < d x
  · rw [farWeight,ite_eq_left ⟨hx,hfar hx⟩,Real.rpow_natCast]
    simpa only [finrank_euclideanSpace_fin] using weight_bound volume hκ hκ1 e x
  · have hx2 : 2 ≤ ‖x‖ := not_lt.mp (fun hh => hx ((d_pos_iff x).mpr hh))
    rw [weight_outer volume κ e hx2,farWeight,ite_eq_right (by simp [hx]),mul_zero]

lemma cap_difference_global {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4)
    (e : sphere (0:Space n) 1) (z : Space n × Space n) :
    |weight volume κ e z.1-weight volume κ e z.2| ≤
      oscillationConstant (volume : Measure (Space n)) κ*δ*(eta n z.1+eta n z.2)+
      boundConstant (volume : Measure (Space n)) κ*(farWeight δ (N n-n:ℕ) z+farWeight δ (N n-n:ℕ) z.swap) := by
  have hC := oscillationConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hB := boundConstant_nonneg (volume : Measure (Space n)) hκ.le
  by_cases hc : 0 < pairGap z ∧ ‖z.1-z.2‖ ≤ δ*pairGap z^(m n)
  · exact (cap_close_bound hn hκ hκ1 hδ.le hδ1 e hc.1 hc.2).trans (le_add_of_nonneg_right
      (mul_nonneg hB (add_nonneg (farWeight_nonneg _ _ _) (farWeight_nonneg _ _ _))))
  · obtain ⟨ha,hb⟩ := far_pair_endpoint hδ.le hc
    have h1 := cap_endpoint_far_bound hn hκ hκ1 e z.1 z.2 ha
    have h2 := cap_endpoint_far_bound hn hκ hκ1 e z.2 z.1 (by simpa only [norm_sub_rev z.2 z.1] using hb)
    have hab : |weight volume κ e z.1-weight volume κ e z.2| ≤ weight volume κ e z.1+weight volume κ e z.2 := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg (weight_nonneg volume κ e _)] using
        abs_sub_le (weight volume κ e z.1) 0 (weight volume κ e z.2)
    exact hab.trans (((add_le_add h1 h2).trans_eq (by simp only [Prod.swap]; ring)).trans
      (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hC hδ.le) (add_nonneg (eta_nonneg n _) (eta_nonneg n _)))))

lemma IsSolution.capMismatch_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (e : sphere (0:Space n) 1) :
    capMismatchIntegral (source u q B) (source v p A) κ e ≤ ENNReal.ofReal
      (oscillationConstant (volume : Measure (Space n)) κ*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+
      boundConstant (volume : Measure (Space n)) κ*(farConstant n p q A B δ+farConstant n q p B A δ)) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hηf := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hηg := h.weight_right hn hp (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have h1 := h.farWeight_bound hn hp hq hδ (by linarith) (cutoff_far_exponents n).2.2
  have h2 := h.farWeight_swap_bound hn hp hq hδ (by linarith) (cutoff_far_exponents n).2.2
  have hηi : Integrable (fun z : Space n × Space n => eta n z.1+eta n z.2) _ := hηf.1.add hηg.1
  have hfi : Integrable (fun z => farWeight δ (N n-n:ℕ) z+farWeight δ (N n-n:ℕ) z.swap) _ := h1.1.add h2.1
  have hi : Integrable (fun z : Space n × Space n =>
      oscillationConstant (volume : Measure (Space n)) κ*δ*(eta n z.1+eta n z.2)+
      boundConstant (volume : Measure (Space n)) κ*(farWeight δ (N n-n:ℕ) z+farWeight δ (N n-n:ℕ) z.swap)) _ :=
    (hηi.const_mul _).add (hfi.const_mul _)
  have hC := oscillationConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hB := boundConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hb := cap_difference_global (by omega : 1 ≤ n) hκ hκ1 hδ hδ1 e
  unfold capMismatchIntegral
  apply (lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hb z))).trans
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z =>
    add_nonneg (mul_nonneg (mul_nonneg hC hδ.le) (add_nonneg (eta_nonneg n _) (eta_nonneg n _)))
      (mul_nonneg hB (add_nonneg (farWeight_nonneg _ _ _) (farWeight_nonneg _ _ _))))),
    integral_add (hηi.const_mul _) (hfi.const_mul _),integral_const_mul,integral_const_mul,
    integral_add hηf.1 hηg.1,integral_add h1.1 h2.1,hηf.2,hηg.2]
  exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add h1.2 h2.2) hB))

end HenonLaneEmden
end
end CapMismatch

end OAI
