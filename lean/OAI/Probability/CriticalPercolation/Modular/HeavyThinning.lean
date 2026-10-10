import Mathlib
import OAI.Probability.CriticalPercolation.Modular.PeakReturn
import OAI.Probability.CriticalPercolation.Modular.PeakRatioTransport
import OAI.Probability.CriticalPercolation.Modular.MarkedTiltedTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma clusterPeakRatio_aut (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeakRatio (φ.edge '' ω) (φ.vertex x) = G.clusterPeakRatio ω x := by
  unfold clusterPeakRatio
  rw [←φ.vertex.tsum_eq]
  simp only [G.peakRatioTransport_aut]

def heavyFlag (p : unitInterval) (u : E → ℝ) (x : V) : Prop :=
  G.modularMass x (G.cluster (atParameter p u) x) = ∞

lemma measurable_heavyFlag (p : unitInterval) (x : V) :
    Measurable (fun u => G.heavyFlag p u x) :=
  ((G.measurable_modularClusterMass x x).comp (measurable_atParameter p)).eq_const ∞

omit [Countable V] [Countable E] in
lemma heavyFlag_iff_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) {x y : V}
    (hxy : (G.openGraph (atParameter q u)).Reachable x y) :
    G.heavyFlag p u x ↔ G.heavyFlag p u y := by
  have hr := hxy.mono (G.openGraph_mono (atParameter_mono u hqp))
  unfold heavyFlag
  rw [G.cluster_eq_of_reachable hr,G.modularMass_eq_top_change_base hc hl x y]

omit [Countable V] [Countable E] in
lemma heavyFlag_aut (φ : G.Aut) (p : unitInterval) (u : E → ℝ) (x : V) :
    G.heavyFlag p (reindexMarks φ.edge u) (φ.vertex x) ↔ G.heavyFlag p u x := by
  unfold heavyFlag
  rw [atParameter_reindex,←φ.cluster_image,φ.modularMass_image]

def heavyRestrictedPeakTransport (p q : unitInterval) (u : E → ℝ) (x y : V) : ℝ≥0∞ :=
  if G.heavyFlag p u x then G.peakRatioTransport (atParameter q u) x y else 0

lemma measurable_heavyRestrictedPeakTransport (p q : unitInterval) (x y : V) :
    Measurable (fun u => G.heavyRestrictedPeakTransport p q u x y) :=
  ((G.measurable_peakRatioTransport x y).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_aut (p q : unitInterval) (φ : G.Aut)
    (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) =
    G.heavyRestrictedPeakTransport p q u x y := by
  simp only [heavyRestrictedPeakTransport,G.heavyFlag_aut,atParameter_reindex,G.peakRatioTransport_aut]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_out (p q : unitInterval) (u : E → ℝ) (x : V) :
    (∑' y, G.heavyRestrictedPeakTransport p q u x y) =
    if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 := by
  by_cases h : G.heavyFlag p u x <;> simp only [heavyRestrictedPeakTransport,h,ite_true,ite_false,
    clusterPeakRatio,tsum_zero]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_swap (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q u x y =
    if G.heavyFlag p u y then G.peakRatioTransport (atParameter q u) x y else 0 := by
  by_cases hy : y∈G.clusterPeaks (atParameter q u) x
  · simp only [heavyRestrictedPeakTransport,G.heavyFlag_iff_of_reachable hc hl hqp u hy.1]
  · simp only [heavyRestrictedPeakTransport,peakRatioTransport,ite_eq_right hy,ite_self]

lemma heavyRestrictedPeakTransport_incoming_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) (y : V) :
    ∀ᵐ u ∂markLaw, (∑' x, G.heavyRestrictedPeakTransport p q u x y * G.stabilizerWeight y x) =
      if G.heavyFlag p u y then G.peakReturn (atParameter q u) y else 0 := by
  have ha := G.marks_ae_of_law_ae q _ (G.peakRatioTransport_incoming_ae hc hl hq q y)
  filter_upwards [ha] with u hu
  simp only [G.heavyRestrictedPeakTransport_swap hc hl hqp]
  by_cases h : G.heavyFlag p u y
  · simpa only [h,ite_true] using hu
  · simp only [h,ite_false,zero_mul,tsum_zero]

lemma expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) =
    ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter q u) x else 0 ∂markLaw := by
  simp_rw [←G.heavyRestrictedPeakTransport_out]
  rw [OrbitRepresentatives.mark_tilted_transport G (G.orbitRepresentatives hq) hc hl
    (G.heavyRestrictedPeakTransport p q) (G.measurable_heavyRestrictedPeakTransport p q)
    (G.heavyRestrictedPeakTransport_aut p q)]
  apply Finset.sum_congr rfl
  intro x _
  exact lintegral_congr_ae (G.heavyRestrictedPeakTransport_incoming_ae hc hl hq hqp x)

lemma tendsto_expected_heavy_peakReturn
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (x : V) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) : Measurable (fun u =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) :=
    ((G.measurable_peakReturn x).comp (measurable_atParameter (q n))).ite
      (G.measurable_heavyFlag p x).setOf measurable_const
  have hbound (n : ℕ) : ∀ᵐ u ∂markLaw,
      (if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) ≤ (1:ℝ≥0∞) := by
    exact Eventually.of_forall (fun u => by split_ifs; exact G.peakReturn_le_one _ x; exact zero_le)
  have hae := G.marks_ae_of_law_ae p _ (G.no_heavy_finite_peaks_ae hc hl hq p)
  have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) atTop (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hae] with u hu
    by_cases h : G.heavyFlag p u x
    · simp only [h,ite_true]
      apply G.tendsto_peakReturn_of_exhaustion _ _
        ((atParameter_mono u).comp hmono) (atParameter_iUnion p q hqp hlim u) x
      by_cases hp : G.clusterPeak (atParameter p u) x
      · right
        intro hf
        exact hu x hf.toFinset.card ⟨h,⟨hf.toFinset,le_rfl,fun _ hy => hf.mem_toFinset.mpr hy⟩,hp⟩
      · exact Or.inl hp
    · simp only [h,ite_false]
      exact tendsto_const_nhds
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => (1:ℝ≥0∞)) hmeas hbound (by simp) ht

theorem tendsto_sum_expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  simp_rw [G.expected_heavy_clusterPeakRatio hc hl hq (hqp _)]
  have ht := tendsto_finsetSum (G.orbitRepresentatives hq).roots
    (fun x _ => G.tendsto_expected_heavy_peakReturn hc hl hq p q hmono hqp hlim x)
  simpa only [Finset.sum_const_zero] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
