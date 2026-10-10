import OAI.Dynamics.StandardMap.LocalTestDetection

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
def SlowPair (d : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ s t, (¬∃w,LocallyAffineAt d s w) → (¬LocallyAffineAt d t 1) → d s t≤ c*|t-s|
lemma interval_window_of_near (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ) (x : ℝ)
    (hu : dist (u:ℝ) x<((1:ℝ)/(2:ℝ)^q)/4)
    (hs : (j.val.1:ℝ)∈ball x (((1:ℝ)/(2:ℝ)^q)/4))
    (ht : (j.val.2:ℝ)∈ball x (((1:ℝ)/(2:ℝ)^q)/4)) : intervalInWindow j u q := by
  have h0 : (0:ℝ)<1/(2:ℝ)^q := by positivity
  rw [Real.dist_eq,abs_lt] at hu
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  constructor <;> linarith [hu.1,hu.2,hs.1,hs.2,ht.1,ht.2]
lemma dyadicBridge_real_sorted (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (hb : DyadicBridgeExclusions d) (s t : ℝ) (hst : s< t)
    (hpq : ((¬∃w,LocallyAffineAt (realArray d) s w) ∧ ¬LocallyAffineAt (realArray d) t 1) ∨
      ((¬LocallyAffineAt (realArray d) s 1) ∧ ¬∃w,LocallyAffineAt (realArray d) t w)) :
    realArray d s t≤(999/1000:ℝ)*(t-s) := by
  by_contra hn
  have hf : (999/1000:ℝ)*(t-s)< realArray d s t := lt_of_not_ge hn
  have ho : IsOpen {p : ℝ×ℝ | (999/1000:ℝ)*(p.2-p.1)< realArray d p.1 p.2} :=
    isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst)) (continuous_realArray d hu)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ho (s,t) hf
  have hz : Tendsto (fun q : ℕ => (1:ℝ)/(2:ℝ)^q) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨q,hqδ,hqgap⟩ := ((hz.eventually (gt_mem_nhds hδ)).and
    (hz.eventually (gt_mem_nhds (show (0:ℝ)<(t-s)/4000 by linarith)))).exists
  let ρ : ℝ := 1/(2:ℝ)^q
  have hρ : 0< ρ := by dsimp [ρ]; positivity
  change ρ< δ at hqδ
  change ρ<(t-s)/4000 at hqgap
  obtain ⟨u,hu'⟩ := denseRange_dyadicTime.exists_dist_lt s (show 0< ρ/4 by positivity)
  obtain ⟨v,hv'⟩ := denseRange_dyadicTime.exists_dist_lt t (show 0< ρ/4 by positivity)
  have hu' : dist (u:ℝ) s< ρ/4 := by rwa [dist_comm]
  have hv' : dist (v:ℝ) t< ρ/4 := by rwa [dist_comm]
  have hfast : (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v := by
    have hh := hball (show ((u:ℝ),(v:ℝ))∈ball (s,t) δ by
      rw [mem_ball,Prod.dist_eq,max_lt_iff]
      exact ⟨hu'.trans (by linarith),hv'.trans (by linarith)⟩)
    change (999/1000:ℝ)*((v:ℝ)-(u:ℝ))<realArray d (u:ℝ) (v:ℝ) at hh
    simpa only [realArray_coe d hu] using hh
  have huabs := abs_lt.mp (show |(u:ℝ)-s|< ρ/4 by simpa only [Real.dist_eq] using hu')
  have hvabs := abs_lt.mp (show |(v:ℝ)-t|< ρ/4 by simpa only [Real.dist_eq] using hv')
  have huv : (u:ℝ)<(v:ℝ) := by linarith [huabs.1,huabs.2,hvabs.1,hvabs.2]
  have hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 := by
    change ρ≤_
    linarith [huabs.1,huabs.2,hvabs.1,hvabs.2]
  rcases hpq with ⟨hs,ht'⟩|⟨hs,ht'⟩
  · obtain ⟨j,hjs,hjt,hj⟩ := local_positive_test d hu ht s hs (ρ/4) (by positivity)
    obtain ⟨l,hls,hlt,hl⟩ := local_positive_shortfall d hu t ht' (ρ/4) (by positivity)
    have hju := testEndpoint_inWindow j u q (interval_window_of_near j u q s hu' hjs hjt)
    have hlv := shortfallEndpoint_inWindow l v q (interval_window_of_near l v q t hv' hls hlt)
    have hh := hb u v q j l true huv hq hju hlv
      (by simpa only [bridgeLeft,ite_eq_left,testEndpoint_value,clippedTest_unit j d hu] using hj)
      (by simpa only [bridgeRight,ite_eq_left,shortfallEndpoint_value,clippedShortfall_unit d hu _ _ l.property] using hl)
    exact (not_lt_of_ge hh) hfast
  · obtain ⟨l,hls,hlt,hl⟩ := local_positive_shortfall d hu s hs (ρ/4) (by positivity)
    obtain ⟨j,hjs,hjt,hj⟩ := local_positive_test d hu ht t ht' (ρ/4) (by positivity)
    have hlu := shortfallEndpoint_inWindow l u q (interval_window_of_near l u q s hu' hls hlt)
    have hjv := testEndpoint_inWindow j v q (interval_window_of_near j v q t hv' hjs hjt)
    have hh := hb u v q j l false huv hq hlu hjv
      (by simpa only [bridgeLeft,Bool.false_eq_true,ite_false,shortfallEndpoint_value,clippedShortfall_unit d hu _ _ l.property] using hl)
      (by simpa only [bridgeRight,Bool.false_eq_true,ite_false,testEndpoint_value,clippedTest_unit j d hu] using hj)
    exact (not_lt_of_ge hh) hfast
lemma dyadicBridge_real_slowPair (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (hb : DyadicBridgeExclusions d) : SlowPair (realArray d) (999/1000) := by
  intro s t hs ht'
  rcases lt_trichotomy s t with hst|hst|hst
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact dyadicBridge_real_sorted d hu ht hb s t hst (Or.inl ⟨hs,ht'⟩)
  · subst t; simp only [realArray_self d hu,sub_self,abs_zero,mul_zero,le_refl]
  · rw [realArray_symm d hu,abs_sub_comm,abs_of_pos (sub_pos.mpr hst)]
    exact dyadicBridge_real_sorted d hu ht hb t s hst (Or.inr ⟨ht',hs⟩)
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma slowPair_aemulti : ∀ᵐd ∂K.multi,SlowPair (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aemulti K,S.tree_aemulti K,S.dyadicBridge_aeselected K true] with d hu ht hb
  exact dyadicBridge_real_slowPair d.val hu ht hb
lemma slowPair_aeterminal : ∀ᵐd ∂K.terminal,SlowPair (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aeterminal K,S.tree_aeterminal K,S.dyadicBridge_aeselected K false] with d hu ht hb
  exact dyadicBridge_real_slowPair d.val hu ht hb
end CriticalScaleSequence
end StandardMapEntropy

end OAI
