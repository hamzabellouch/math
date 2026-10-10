import OAI.Probability.BenjaminiSchramm.PeakFirstMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def peakBandTransport (a b : ℝ≥0∞) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  G.normalizedPeakTransport ω x y *
    if a ≤ G.stabilizerWeight y x ∧ G.stabilizerWeight y x ≤ b then 1 else 0

def reverseWeightHit (b : ℝ≥0∞) (x : V) : Set (Set E) :=
  {ω | ∃ y, y ∈ G.cluster ω x ∧ G.stabilizerWeight y x ≤ b}

def clusterBandCount (a b : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if y ∈ G.cluster ω x ∧ a ≤ G.stabilizerWeight x y ∧
    G.stabilizerWeight x y ≤ b then 1 else 0

lemma measurable_peakBandTransport [Countable V] [Countable E]
    (a b : ℝ≥0∞) (x y : V) :
    Measurable (fun ω => G.peakBandTransport a b ω x y) :=
  (G.measurable_normalizedPeakTransport x y).mul_const _

lemma peakBandTransport_aut (a b : ℝ≥0∞) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.peakBandTransport a b (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.peakBandTransport a b ω x y := by
  simp only [peakBandTransport, G.normalizedPeakTransport_aut, Aut.stabilizerWeight]

lemma measurableSet_reverseWeightHit [Countable V] [Countable E]
    (b : ℝ≥0∞) (x : V) : MeasurableSet (G.reverseWeightHit b x) :=
  (Measurable.exists fun y => (G.measurable_reachable x y).and measurable_const).setOf

lemma peakBandTransport_outgoing (a b : ℝ≥0∞) (ω : Set E) (x : V) :
    (∑' y, G.peakBandTransport a b ω x y) ≤
      if ω ∈ G.reverseWeightHit b x then 1 else 0 := by
  by_cases hh : ω ∈ G.reverseWeightHit b x
  · rw [ite_eq_left hh]
    apply le_trans _ (G.normalizedPeakTransport_outgoing ω x)
    apply ENNReal.tsum_le_tsum
    intro y
    unfold peakBandTransport
    split_ifs <;> simp
  · rw [ite_eq_right hh]
    apply le_of_eq (ENNReal.tsum_eq_zero.mpr _)
    intro y
    unfold peakBandTransport normalizedPeakTransport
    by_cases hy : y ∈ G.clusterPeaks ω x
    · have hb : ¬ (a ≤ G.stabilizerWeight y x ∧ G.stabilizerWeight y x ≤ b) :=
        fun hb => hh ⟨y,hy.1,hb.2⟩
      simp [hb]
    · simp [hy]

lemma peakBandTransport_incoming_lower (a b : ℝ≥0∞) (ω : Set E) (y : V) :
    a * G.peakReturn ω y * G.clusterBandCount a b ω y ≤
      ∑' x, G.peakBandTransport a b ω x y * G.stabilizerWeight y x := by
  rw [clusterBandCount, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  rw [peakBandTransport, G.normalizedPeakTransport_eq_reverse]
  by_cases hx : x ∈ G.cluster ω y
  · simp only [hx, true_and, ↓reduceIte]
    by_cases hb : a ≤ G.stabilizerWeight y x ∧ G.stabilizerWeight y x ≤ b
    · simp only [ite_eq_left hb, mul_one]
      rw [mul_comm a]
      gcongr
      exact hb.1
    · simp [hb]
  · simp [hx]

theorem expected_peakBandCount_le_reverseWeightHit [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (a b : ℝ≥0∞) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, a * G.peakReturn ω x * G.clusterBandCount a b ω x ∂G.law p) ≤
      ∑ x ∈ (G.orbitRepresentatives hq).roots, G.law p (G.reverseWeightHit b x) := by
  calc
    _ ≤ ∑ y ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ∑' x, G.peakBandTransport a b ω x y * G.stabilizerWeight y x ∂G.law p := by
      apply Finset.sum_le_sum
      intro y _
      exact lintegral_mono fun ω => G.peakBandTransport_incoming_lower a b ω y
    _ = ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ∑' y, G.peakBandTransport a b ω x y ∂G.law p :=
      (OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
        (G.peakBandTransport a b) (G.measurable_peakBandTransport a b)
        (G.peakBandTransport_aut a b)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      apply le_trans (lintegral_mono fun ω => G.peakBandTransport_outgoing a b ω x)
      simpa only [Set.indicator, Pi.one_apply] using
        (lintegral_indicator_one (μ := G.law p) (G.measurableSet_reverseWeightHit b x)).le

end CriticalPercolation.BondGraph

end

end OAI
