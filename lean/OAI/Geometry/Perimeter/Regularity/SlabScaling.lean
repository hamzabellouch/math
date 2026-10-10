import OAI.Geometry.Perimeter.Regularity.FlatnessImprovement

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem FullSlab.mono_height {E : Set (Euc n)} {v : Euc n} {R a b : ℝ}
    (h : FullSlab E v R a) (hab : a≤b) : FullSlab E v R b := by
  refine ⟨fun x hx ↦ (h.1 x hx).trans hab,?_⟩
  filter_upwards [h.2] with x hx
  exact fun hball hheight ↦ hx hball (hab.trans_lt hheight)

theorem FullSlab.dilate {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} {R a t : ℝ} (h : FullSlab E v R a) (ht : 0 < t) :
    FullSlab (blownUpSet E 0 t) v (R/t) (a/t) := by
  have hball (x : Euc n) (hx : x∈Metric.ball 0 (R/t)) : t•x∈Metric.ball 0 R := by
    simp only [Metric.mem_ball,dist_zero_right] at hx ⊢
    rw [norm_smul,Real.norm_of_nonneg ht.le]
    simpa only [mul_comm] using (lt_div_iff₀ ht).mp hx
  refine ⟨?_,?_⟩
  · intro x hx
    have hs : t•x∈perimeterSupport E := by
      simpa only [zero_add] using (perimeterSupport_blownUpSet hE 0 ht x).mp hx.1
    have hh := h.1 (t•x) ⟨hs,hball x hx.2⟩
    rw [real_inner_smul_right,abs_mul,abs_of_pos ht] at hh
    exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hh)
  · have hh := (Measure.quasiMeasurePreserving_smul volume ht.ne').ae h.2
    filter_upwards [hh] with x hx
    intro hxb hxa
    have hb : a < |inner ℝ v (t•x)| := by
      rw [real_inner_smul_right,abs_mul,abs_of_pos ht]
      simpa only [mul_comm] using (div_lt_iff₀ ht).mp hxa
    have he := hx (hball x hxb) hb
    change (0+t•x∈E ↔ inner ℝ v x < 0)
    rw [zero_add,he,real_inner_smul_right]
    constructor
    · intro hh; nlinarith
    · exact fun hh ↦ mul_neg_of_pos_of_neg ht hh

theorem FullSlab.recenter_half {E : Set (Euc n)} (hE : MeasurableSet E)
    {v p : Euc n} {a : ℝ} (ha : 0≤a) (h : FullSlab E v 8 a)
    (hp : p∈perimeterSupport E ∩ Metric.ball 0 1) :
    FullSlab (blownUpSet E p (1/2)) v 8 (4*a) := by
  have hhp : |inner ℝ v p|≤a := h.1 p ⟨hp.1,Metric.ball_subset_ball (by norm_num) hp.2⟩
  have hball (x : Euc n) (hx : x∈Metric.ball 0 8) : p+(1/2:ℝ)•x∈Metric.ball 0 8 := by
    have hnp : ‖p‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hp.2
    have hnx : ‖x‖<8 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hh := norm_add_le p ((1/2:ℝ)•x)
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hh
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  refine ⟨?_,?_⟩
  · intro x hx
    have hs := (perimeterSupport_blownUpSet hE p (by norm_num : (0:ℝ)<1/2) x).mp hx.1
    have hh := h.1 _ ⟨hs,hball x hx.2⟩
    rw [inner_add_right,real_inner_smul_right] at hh
    rcases abs_le.mp hh with ⟨hl,hu⟩
    rcases abs_le.mp hhp with ⟨hpl,hpu⟩
    apply abs_le.mpr
    constructor <;> linarith
  · have hq : Measure.QuasiMeasurePreserving (fun x : Euc n ↦ p+(1/2:ℝ)•x) volume volume :=
      (measurePreserving_add_left volume p).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul volume (by norm_num : (1/2:ℝ)≠0))
    filter_upwards [hq.ae h.2] with x hx
    intro hxb hxa
    rcases abs_le.mp hhp with ⟨hpl,hpu⟩
    have hi : inner ℝ v (p+(1/2:ℝ)•x)=inner ℝ v p+1/2*inner ℝ v x := by
      rw [inner_add_right,real_inner_smul_right]
    have hbig : a < |inner ℝ v (p+(1/2:ℝ)•x)| := by
      rw [hi]
      rcases lt_abs.mp hxa with hh | hh
      · exact (lt_of_lt_of_le (by linarith) (le_abs_self _))
      · exact (lt_of_lt_of_le (by linarith) (neg_le_abs _))
    have hsign : inner ℝ v (p+(1/2:ℝ)•x)<0 ↔ inner ℝ v x<0 := by
      rw [hi]
      rcases lt_abs.mp hxa with hh | hh
      · have hpos : 0 < inner ℝ v x := by linarith
        constructor <;> intro hneg <;> linarith
      · have hneg : inner ℝ v x < 0 := by linarith
        constructor <;> intro hneg' <;> linarith
    exact (hx (hball x hxb) hbig).trans hsign

end RPISingularHarnack

end

end OAI
