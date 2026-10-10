import OAI.Geometry.Perimeter.Regularity.FlatnessImprovement

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem positive_cap_ball {v w : Euc n} (hv : ‖v‖=1)
    {r : ℝ} (hr : 0 < r) (hvw : ‖w-v‖≤1/4) :
    ∀ x∈Metric.ball ((r/2)•v) (r/8),
      x∈Metric.ball 0 r ∧ r/8 < inner ℝ v x ∧ r/8 < inner ℝ w x := by
  intro x hx
  have hxc : ‖x-(r/2)•v‖ < r/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hc : ‖(r/2)•v‖=r/2 := by rw [norm_smul,Real.norm_of_nonneg (by positivity),hv,mul_one]
  have hnx : ‖x‖<r := by
    have hh := norm_le_norm_sub_add x ((r/2)•v)
    rw [hc] at hh
    linarith
  have hi : inner ℝ v ((r/2)•v)=r/2 := by
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hv]; ring
  have hvi := abs_real_inner_le_norm v (x-(r/2)•v)
  rw [inner_sub_right,hi,hv,one_mul] at hvi
  have hvx : 3*r/8 < inner ℝ v x := by
    have hh := (abs_le.mp hvi).1
    linarith
  have hwi := abs_real_inner_le_norm (w-v) x
  rw [inner_sub_left] at hwi
  have hwb : ‖w-v‖*‖x‖ < r/4 :=
    (mul_le_mul_of_nonneg_right hvw (norm_nonneg x)).trans_lt (by linarith)
  have hwx : r/8 < inner ℝ w x := by
    have hh := (abs_le.mp hwi).1
    linarith
  exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hnx,by linarith,hwx⟩

theorem FullSlab.restore_phase (hn : 1 < n) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {v w : Euc n} (hv : ‖v‖=1)
    {R r a b : ℝ} (hslab : FullSlab E v R a) (hr : 0 < r) (hrR : r≤R)
    (ha : a<r/8) (hb : 0≤b) (hbr : b<r/8) (hvw : ‖w-v‖≤1/4)
    (hheight : ∀ x∈perimeterSupport E ∩ Metric.ball 0 r, |inner ℝ w x|≤b) :
    FullSlab E w r b := by
  let A : Set (Euc n) := Metric.ball ((r/2)•v) (r/8)
  let B : Set (Euc n) := {x : Euc n | -x∈A}
  have hA := positive_cap_ball hv hr hvw
  have hAcap : A ⊆ Metric.ball 0 r ∩ {x | b < inner ℝ w x} := by
    intro x hx
    exact ⟨(hA x hx).1,hbr.trans (hA x hx).2.2⟩
  have hBcap : B ⊆ Metric.ball 0 r ∩ {x | inner ℝ w x < -b} := by
    intro x hx
    have hh := hA (-x) hx
    refine ⟨by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hh.1,?_⟩
    simp only [inner_neg_right] at hh
    change inner ℝ w x < -b
    linarith [hh.2.2]
  have hAE : ∀ᵐ x ∂volume, x∈A → x∉E := by
    filter_upwards [hslab.2] with x hx
    intro hxA hxE
    have hh := hA x hxA
    have hpos : 0 < inner ℝ v x := lt_trans (by positivity) hh.2.1
    have he := hx (Metric.ball_subset_ball hrR hh.1)
      (by rw [abs_of_pos hpos]; exact ha.trans hh.2.1)
    exact (not_lt_of_ge hpos.le) (he.mp hxE)
  have hBE : ∀ᵐ x ∂volume, x∈B → x∈E := by
    filter_upwards [hslab.2] with x hx
    intro hxB
    have hh := hA (-x) hxB
    have hball : x∈Metric.ball 0 R := Metric.ball_subset_ball hrR
      (by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hh.1)
    have hneg : inner ℝ v x < 0 := by simp only [inner_neg_right] at hh; linarith [hh.2.1]
    apply (hx hball ?_).mpr hneg
    rw [abs_of_neg hneg]
    simp only [inner_neg_right] at hh
    exact ha.trans hh.2.1
  have hvolA : 0 < volume (A\E) := by
    have he : A\E =ᵐ[volume] A := by
      filter_upwards [hAE] with x hx
      exact propext ⟨fun h ↦ h.1,fun h ↦ ⟨h,hx h⟩⟩
    have heq : volume (A \ E)=volume A := measure_congr he
    rw [heq]
    exact Metric.measure_ball_pos volume _ (by positivity)
  have hvolB : 0 < volume (B∩E) := by
    have he : (B ∩ E : Set (Euc n)) =ᵐ[volume] B := by
      filter_upwards [hBE] with x hx
      exact propext ⟨fun h ↦ h.1,fun h ↦ ⟨h,hx h⟩⟩
    have heq : volume (B ∩ E)=volume B := measure_congr he
    rw [heq]
    have heB : B=Metric.ball (-(r/2)•v) (r/8) := by
      ext x
      change dist (-x) ((r/2)•v)<r/8 ↔ dist x (-(r/2)•v)<r/8
      rw [neg_smul]
      have hd : dist (-x) ((r/2)•v)=dist x (-((r/2)•v)) := by
        simpa only [neg_neg] using dist_neg_neg x (-((r/2)•v))
      rw [hd]
    rw [heB]
    exact Metric.measure_ball_pos volume _ (by positivity)
  exact ⟨hheight,minimizing_slab_phase_agreement hn hmin w hb hheight
    hAcap hBcap hvolA hvolB⟩

end RPISingularHarnack

end

end OAI
