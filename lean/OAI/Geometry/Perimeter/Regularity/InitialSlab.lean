import OAI.Geometry.Perimeter.Regularity.PhaseRestoration

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem phase_anchors_of_small_symmDiff {E H A B U : Set (Euc n)}
    (hE : MeasurableSet E) (hU : volume U ≠ (∞ : ℝ≥0∞))
    (hA : A ⊆ U ∩ Hᶜ) (hB : B ⊆ U ∩ H)
    (hsmallA : volume.real (symmDiff E H ∩ U) < volume.real A)
    (hsmallB : volume.real (symmDiff E H ∩ U) < volume.real B) :
    0 < volume (A\E) ∧ 0 < volume (B∩E) := by
  have hfin : volume (symmDiff E H ∩ U) ≠ (∞ : ℝ≥0∞) := measure_ne_top_of_subset inter_subset_right hU
  constructor
  · by_contra! hz
    have heq : volume A = volume (A∩E) := by
      have hh := measure_sdiff_add_inter (μ := volume) A hE
      rw [le_antisymm hz bot_le,zero_add] at hh
      exact hh.symm
    have hle : volume (A∩E) ≤ volume (symmDiff E H ∩ U) := by
      apply measure_mono
      intro x hx
      exact ⟨Or.inl ⟨hx.2,(hA hx.1).2⟩,(hA hx.1).1⟩
    have hh := ENNReal.toReal_mono hfin (heq ▸ hle)
    exact (not_lt_of_ge hh) hsmallA
  · by_contra! hz
    have heq : volume B = volume (B\E) := by
      have hh := measure_sdiff_add_inter (μ := volume) B hE
      rw [le_antisymm hz bot_le,add_zero] at hh
      exact hh.symm
    have hle : volume (B\E) ≤ volume (symmDiff E H ∩ U) := by
      apply measure_mono
      intro x hx
      exact ⟨Or.inr ⟨(hB hx.1).2,hx.2⟩,(hB hx.1).1⟩
    have hh := ENNReal.toReal_mono hfin (heq ▸ hle)
    exact (not_lt_of_ge hh) hsmallB

theorem HasHalfspaceBlowup.eventually_fullSlab (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hbl : HasHalfspaceBlowup E p v)
    (r : ℕ → ℝ) (hr : ∀ i, 0<r i) (htr : Tendsto r atTop (𝓝 0))
    {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∀ᶠ i in atTop, FullSlab (blownUpSet E p (r i)) v 8 a := by
  let H : Set (Euc n) := {x | inner ℝ x v<0}
  let A : Set (Euc n) := Metric.ball ((4:ℝ)•v) 1
  let B : Set (Euc n) := Metric.ball ((-4:ℝ)•v) 1
  have hAcap : A ⊆ Metric.ball 0 8 ∩ {x | a < inner ℝ v x} := by
    intro x hx
    have hh := positive_cap_ball hbl.1 (by norm_num : (0:ℝ)<8)
      (by simp : ‖v-v‖≤1/4) x (by simpa only [show (8:ℝ)/2=4 by norm_num,show (8:ℝ)/8=1 by norm_num] using (show x∈Metric.ball ((4:ℝ)•v) 1 from hx))
    exact ⟨hh.1,ha1.trans (by simpa using hh.2.1)⟩
  have hBcap : B ⊆ Metric.ball 0 8 ∩ {x | inner ℝ v x < -a} := by
    intro x hx
    have hxA : -x∈A := by
      change dist (-x) ((4:ℝ)•v)<1
      have he : dist (-x) ((4:ℝ)•v)=dist x ((-4:ℝ)•v) := by
        simpa only [neg_smul,neg_neg] using dist_neg_neg x (-((4:ℝ)•v))
      rw [he]
      exact hx
    have hh := hAcap hxA
    refine ⟨by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hh.1,?_⟩
    have hi := hh.2
    simp only [mem_ofPred_eq,inner_neg_right] at hi
    change inner ℝ v x < -a
    linarith
  have hApos : 0<volume.real A := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    (measure_ball_lt_top.ne)
  have hBpos : 0<volume.real B := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ (by norm_num : (0:ℝ)<1)).ne'
    (measure_ball_lt_top.ne)
  have ht := hbl.local_L1 hmin.1 r hr htr (0:Euc n) 8 (by norm_num)
  have hheight := hbl.support_height hn hmin r hr htr (isCompact_closedBall (0:Euc n) 8) ha
  filter_upwards [ht.eventually (gt_mem_nhds hApos),ht.eventually (gt_mem_nhds hBpos),hheight] with i hAi hBi hhi
  have hm := locally_minimizing_blownUpSet hmin p (hr i)
  have hh : ∀ x∈perimeterSupport (blownUpSet E p (r i)) ∩ Metric.ball 0 8,
      |inner ℝ v x|≤a := by
    intro x hx
    rw [real_inner_comm]
    exact (hhi x ⟨hx.1,Metric.ball_subset_closedBall hx.2⟩).le
  have hAU : A ⊆ Metric.closedBall 0 8 ∩ Hᶜ := by
    intro x hx
    have hhA := hAcap hx
    refine ⟨Metric.ball_subset_closedBall hhA.1,?_⟩
    change ¬inner ℝ x v<0
    rw [real_inner_comm]
    exact not_lt_of_ge (ha.le.trans hhA.2.le)
  have hBU : B ⊆ Metric.closedBall 0 8 ∩ H := by
    intro x hx
    have hhB := hBcap hx
    refine ⟨Metric.ball_subset_closedBall hhB.1,?_⟩
    change inner ℝ x v<0
    rw [real_inner_comm]
    exact hhB.2.trans (neg_neg_of_pos ha)
  obtain ⟨hvolA,hvolB⟩ := phase_anchors_of_small_symmDiff hm.1
    (isCompact_closedBall (0:Euc n) 8).measure_ne_top hAU hBU hAi hBi
  exact ⟨hh,minimizing_slab_phase_agreement hn hm v ha.le hh hAcap hBcap hvolA hvolB⟩

end RPISingularHarnack

end

end OAI
