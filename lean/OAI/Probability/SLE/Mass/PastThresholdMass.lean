import OAI.Probability.SLE.Gauge.StrictPastCountable
import OAI.Probability.SLE.Geometry.WeightedCompactTerminal

namespace OAI

/-! Continuous mass crosses an intermediate level at a dense test time.
Consequently a cell with twice the threshold has at least half its mass
strictly after a successful past test. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

lemma dense_time_between_mass_levels (q : ℕ → ℝ≥0) (hq : DenseRange q)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (h0 : f 0=0)
    (M H L : ℝ) (hH : 0<H) (hHL : H<L) (hLM : L<M)
    (hlim : Tendsto f atTop (𝓝 M)) : ∃ n, H<f (q n) ∧ f (q n)<L := by
  obtain ⟨T,hT⟩ := (hlim.eventually (lt_mem_nhds hLM)).exists
  obtain ⟨t,_,ht⟩ := intermediate_value_Icc (show (0:ℝ≥0)≤T from bot_le)
    hf.continuousOn (show (H+L)/2∈Icc (f 0) (f T) by rw [h0]; constructor <;> linarith)
  have hopen : IsOpen (f ⁻¹' Ioo H L) := isOpen_Ioo.preimage hf
  have hne : (f ⁻¹' Ioo H L).Nonempty := ⟨t,by change H<f t ∧ f t<L; rw [ht]; constructor <;> linarith⟩
  exact hq.exists_mem_open hopen hne

lemma past_threshold_detects_half
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (hfin : μ K≠∞)
    (A : ℝ≥0 → Set X) (hA : ∀ t, MeasurableSet (A t))
    (q : ℕ → ℝ≥0) (hq : DenseRange q) (f : ℝ≥0 → ℝ)
    (hf : Continuous f) (h0 : f 0=0)
    (hlim : Tendsto f atTop (𝓝 (μ K).toReal))
    (hpast : ∀ n, μ (K ∩ A (q n))=ENNReal.ofReal (f (q n)))
    (H : ℝ) (hH : 0<H) (hlarge : ENNReal.ofReal (2*H)<μ K) :
    μ K≤2*μ (K ∩ ⋃ n, if H<f (q n) then (A (q n))ᶜ else ∅) := by
  have hreal : 2*H<(μ K).toReal := by
    have he := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).2 hlarge
    simpa only [ENNReal.toReal_ofReal (by positivity : 0≤2*H)] using he
  obtain ⟨n,hnH,hnM⟩ := dense_time_between_mass_levels q hq f hf h0 (μ K).toReal H
    ((μ K).toReal/2) hH (by linarith) (by linarith) hlim
  have hsub : K \ A (q n) ⊆ K ∩ ⋃ n, if H<f (q n) then (A (q n))ᶜ else ∅ := by
    intro x hx
    exact ⟨hx.1,mem_iUnion.mpr ⟨n,by rw [ite_eq_left hnH]; exact hx.2⟩⟩
  have hfuture : μ K≤2*μ (K \ A (q n)) := by
    have he := measure_inter_add_sdiff (μ:=μ) K (hA (q n))
    rw [hpast n] at he
    have hd : μ (K \ A (q n))≠∞ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
    have hsum := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hd,
      ENNReal.toReal_ofReal (hH.trans hnH).le] at hsum
    apply (ENNReal.toReal_le_toReal hfin (ENNReal.mul_ne_top (by norm_num) hd)).mp
    rw [ENNReal.toReal_mul]
    norm_num only [ENNReal.toReal_ofNat]
    linarith
  exact hfuture.trans (mul_le_mul' (show (2:ℝ≥0∞)≤2 from le_rfl) (measure_mono hsub))

end SLEExactGauge.Multipoint

end

end OAI
