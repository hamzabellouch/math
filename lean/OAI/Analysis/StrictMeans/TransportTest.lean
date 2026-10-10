import OAI.Analysis.StrictMeans.NormalizedTargets

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def transportTest (k N : ℝ) : DiskFamily × UpperHalfPlane → ℝ≥0∞ :=
  (truncatedPairingDomain k N).indicator (fun q => ENNReal.ofReal (partnerRatio k q))

lemma measurable_transportTest {k : ℝ} (hk : 0 < k) (N : ℝ) :
    Measurable (transportTest k N) :=
  (measurable_partnerRatio hk).ennreal_ofReal.indicator (measurableSet_truncatedPairingDomain hk N)

lemma transportTest_rebase {k : ℝ} (hk : 0 < k) (N : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    transportTest k N (f,z) = transportTest k N (rebase f z,UpperHalfPlane.I) := by
  classical
  unfold transportTest
  have he := truncatedPairingDomain_rebase hk N f z UpperHalfPlane.I
  rw [affineProduct_I] at he
  by_cases hq : (f,z)∈truncatedPairingDomain k N
  · rw [indicator_of_mem hq,indicator_of_mem (he.mpr hq),partnerRatio_rebase hk,
      affineProduct_I]
  · rw [indicator_of_notMem hq,indicator_of_notMem (fun hh=>hq (he.mp hh))]

lemma truncatedPairingDomain_mono {k N M : ℝ} (hN : 0 < N) (hNM : N ≤ M) :
    truncatedPairingDomain k N ⊆ truncatedPairingDomain k M := by
  intro q hq
  exact ⟨hq.1,(one_div_le_one_div_of_le hN hNM).trans hq.2.1,
    hq.2.2.1.trans hNM,hq.2.2.2.trans (mul_le_mul_of_nonneg_right hNM q.2.im_pos.le)⟩

lemma mem_truncatedPairingDomain_eventually {k : ℝ} {q : DiskFamily × UpperHalfPlane}
    (hq : q∈sourcePairingDomain k) :
    ∀ᶠ n : ℕ in atTop, q∈truncatedPairingDomain k (n+1) := by
  let r := (sourcePartner k q).im / q.2.im
  have hr : 0 < r := div_pos (sourcePartner k q).im_pos q.2.im_pos
  obtain ⟨N,hN⟩ := exists_nat_ge (max (1/r) (max r (|(sourcePartner k q).re-q.2.re|/q.2.im)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n+1 := by exact_mod_cast (by omega : N≤n+1)
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have h1 : 1/r ≤ n+1 := (le_max_left _ _).trans (hN.trans hNn)
  refine ⟨hq,?_,(le_max_left _ _).trans ((le_max_right _ _).trans (hN.trans hNn)),?_⟩
  · exact (div_le_iff₀ hn0).mpr (by nlinarith [(div_le_iff₀ hr).mp h1])
  · exact (div_le_iff₀ q.2.im_pos).mp ((le_max_right _ _).trans
      ((le_max_right _ _).trans (hN.trans hNn)))

lemma transportTest_nat_monotone {k : ℝ} (q : DiskFamily × UpperHalfPlane) :
    Monotone (fun n : ℕ => transportTest k (n+1) q) := by
  intro n m hnm
  apply indicator_le_indicator_of_subset (truncatedPairingDomain_mono (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hnm))
  exact fun _ => bot_le

lemma iSup_transportTest {k : ℝ} (q : DiskFamily × UpperHalfPlane) :
    (⨆ n : ℕ,transportTest k (n+1) q)=ENNReal.ofReal (partnerRatio k q) := by
  classical
  by_cases hq : q∈sourcePairingDomain k
  · obtain ⟨n,hn⟩ := (mem_truncatedPairingDomain_eventually hq).exists
    apply le_antisymm
    · apply iSup_le
      intro m
      exact (indicator_le_self' (fun _ _ => bot_le)) q
    · rw [← indicator_of_mem hn (fun q => ENNReal.ofReal (partnerRatio k q))]
      exact le_iSup (fun n : ℕ=>transportTest k (n+1) q) n
  · have he : partnerRatio k q=0 := by simp [partnerRatio,hq]
    rw [he,ENNReal.ofReal_zero]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    exact le_of_eq (indicator_of_notMem (fun h=>hq h.1) _)

end
end StrictInverseFirstPower

end

end OAI
