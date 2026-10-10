import OAI.Probability.CriticalPercolation.Modular.PeakReturn

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def boundedPeakTransport (N : ℕ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ G.clusterPeaks ω x ∧ G.peakBound N ω x then 1 else 0

def boundedPeakMass (N : ℕ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeak ω x ∧ G.peakBound N ω x then G.modularMass x (G.cluster ω x) else 0

lemma measurable_boundedPeakTransport [Countable V] [Countable E] (N : ℕ) (x y : V) :
    Measurable (fun ω => G.boundedPeakTransport N ω x y) := by
  exact measurable_const.ite
    (((G.measurable_mem_clusterPeaks x y).and (G.measurable_peakBound N x)).setOf)
    measurable_const

lemma boundedPeakTransport_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.boundedPeakTransport N (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.boundedPeakTransport N ω x y := by
  unfold boundedPeakTransport
  rw [← φ.clusterPeaks_image, φ.peakBound_iff]
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]

lemma boundedPeakTransport_outgoing (N : ℕ) (ω : Set E) (x : V) :
    (∑' y, G.boundedPeakTransport N ω x y) ≤ N := by
  by_cases hb : G.peakBound N ω x
  · obtain ⟨S,hS,hcover⟩ := hb
    rw [tsum_eq_sum (s := S) (fun y hy => by
      simp only [boundedPeakTransport]
      exact ite_eq_right (fun hh => hy (hcover hh.1)))]
    calc
      _ ≤ ∑ _y ∈ S, (1 : ℝ≥0∞) := Finset.sum_le_sum fun y _ => by
        simp only [boundedPeakTransport]
        split_ifs <;> simp
      _ = (S.card : ℝ≥0∞) := by simp
      _ ≤ N := by exact_mod_cast hS
  · simp [boundedPeakTransport, hb]

lemma boundedPeakTransport_incoming (N : ℕ) (ω : Set E) (y : V) :
    (∑' x, G.boundedPeakTransport N ω x y * G.stabilizerWeight y x) =
      G.boundedPeakMass N ω y := by
  by_cases hy : G.clusterPeak ω y ∧ G.peakBound N ω y
  · rw [boundedPeakMass, ite_eq_left hy]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ G.cluster ω y
    · have hb : G.peakBound N ω x :=
        (G.peakBound_iff_of_reachable N hx).mp hy.2
      have hxy : y ∈ G.clusterPeaks ω x ∧ G.peakBound N ω x := ⟨⟨hx.symm,hy.1⟩,hb⟩
      simp only [boundedPeakTransport, ite_eq_left hxy, one_mul, ite_eq_left hx]
    · have hn : ¬ (y ∈ G.clusterPeaks ω x ∧ G.peakBound N ω x) :=
        fun hh => hx hh.1.1.symm
      simp only [boundedPeakTransport, ite_eq_right hn, zero_mul, ite_eq_right hx]
  · rw [boundedPeakMass, ite_eq_right hy]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    have hn : ¬ (y ∈ G.clusterPeaks ω x ∧ G.peakBound N ω x) := by
      intro hh
      exact hy ⟨hh.1.2,(G.peakBound_iff_of_reachable N hh.1.1).mp hh.2⟩
    simp only [boundedPeakTransport, ite_eq_right hn, zero_mul]

theorem expected_boundedPeakMass_sum [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (N : ℕ) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.boundedPeakMass N ω x ∂G.law p) ≤
        ((G.orbitRepresentatives hq).roots.card : ℝ≥0∞) * N := by
  rw [← show (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, ∑' y, G.boundedPeakTransport N ω x y ∂G.law p) =
      ∑ y ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, G.boundedPeakMass N ω y ∂G.law p from by
    rw [OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
      (G.boundedPeakTransport N) (G.measurable_boundedPeakTransport N)
      (G.boundedPeakTransport_aut N)]
    simp_rw [G.boundedPeakTransport_incoming]]
  calc
    _ ≤ ∑ _x ∈ (G.orbitRepresentatives hq).roots, (N : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro x _
      exact (lintegral_mono fun ω => G.boundedPeakTransport_outgoing N ω x).trans_eq
        (by simp)
    _ = _ := by simp [nsmul_eq_mul]

lemma measurable_boundedPeakMass [Countable V] [Countable E] (N : ℕ) (x : V) :
    Measurable (fun ω => G.boundedPeakMass N ω x) := by
  exact (G.measurable_modularClusterMass x x).ite
    (((G.measurable_clusterPeak x).and (G.measurable_peakBound N x)).setOf)
    measurable_const

lemma boundedPeakMass_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x : V) :
    G.boundedPeakMass N (φ.edge '' ω) (φ.vertex x) = G.boundedPeakMass N ω x := by
  unfold boundedPeakMass
  rw [← φ.cluster_image, φ.modularMass_image, φ.clusterPeak_iff, φ.peakBound_iff]

theorem expected_boundedPeakMass [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (N : ℕ) (x : V) :
    (∫⁻ ω, G.boundedPeakMass N ω x ∂G.law p) ≤
      ((G.orbitRepresentatives hq).roots.card : ℝ≥0∞) * N := by
  obtain ⟨y,hy,φ,rfl⟩ := (G.orbitRepresentatives hq).cover x
  have he : (∫⁻ ω, G.boundedPeakMass N ω (φ.vertex y) ∂G.law p) =
      ∫⁻ ω, G.boundedPeakMass N ω y ∂G.law p := by
    conv_lhs => rw [← G.law_map_aut p φ]
    rw [lintegral_map (G.measurable_boundedPeakMass N _) (BernoulliProduct.measurable_image_equiv φ.edge)]
    simp only [G.boundedPeakMass_aut]
  rw [he]
  exact (Finset.single_le_sum (fun _ _ => zero_le) hy).trans
    (G.expected_boundedPeakMass_sum hc hl hq p N)

def boundedPeakUpperLayerCount (N : ℕ) (a : ℝ≥0∞) (ω : Set E) (y : V) : ℝ≥0∞ :=
  if G.clusterPeak ω y ∧ G.peakBound N ω y then
    ∑' x, if x ∈ G.cluster ω y ∧ a ≤ G.stabilizerWeight y x then 1 else 0
  else 0

lemma measurable_boundedPeakUpperLayerCount [Countable V] [Countable E]
    (N : ℕ) (a : ℝ≥0∞) (y : V) :
    Measurable (fun ω => G.boundedPeakUpperLayerCount N a ω y) := by
  apply Measurable.ite
    (((G.measurable_clusterPeak y).and (G.measurable_peakBound N y)).setOf) _ measurable_const
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (((G.measurable_reachable y x).and measurable_const).setOf)
    measurable_const

lemma weighted_boundedPeakUpperLayerCount (N : ℕ) (a : ℝ≥0∞) (ω : Set E) (y : V) :
    a * G.boundedPeakUpperLayerCount N a ω y ≤ G.boundedPeakMass N ω y := by
  unfold boundedPeakUpperLayerCount boundedPeakMass
  split_ifs with hp
  · rw [modularMass, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : x ∈ G.cluster ω y
    · simp only [hx, true_and, ↓reduceIte]
      by_cases ha : a ≤ G.stabilizerWeight y x
      · simpa only [ite_eq_left ha, mul_one] using ha
      · simp [ha]
    · simp [hx]
  · simp

theorem expected_boundedPeakUpperLayerCount [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (N : ℕ) (a : ℝ≥0∞) (y : V) :
    a * (∫⁻ ω, G.boundedPeakUpperLayerCount N a ω y ∂G.law p) ≤
      ((G.orbitRepresentatives hq).roots.card : ℝ≥0∞) * N := by
  rw [← lintegral_const_mul _ (G.measurable_boundedPeakUpperLayerCount N a y)]
  exact (lintegral_mono fun ω => G.weighted_boundedPeakUpperLayerCount N a ω y).trans
    (G.expected_boundedPeakMass hc hl hq p N y)

end CriticalPercolation.BondGraph

end

end OAI
