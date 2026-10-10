import Mathlib
import OAI.Probability.CriticalPercolation.Modular.HeavyPeaks
import OAI.Probability.CriticalPercolation.Modular.PeakRatioTransport
import OAI.Probability.CriticalPercolation.Modular.RandomTiltedTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakReturn (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeak ω x then ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹ else 0

lemma measurable_peakReturn [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.peakReturn ω x) := by
  apply Measurable.ite (G.measurable_clusterPeak x).setOf _ measurable_const
  apply Measurable.inv
  apply (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
  apply measurable_encard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakReturn_eq_inv_ncard (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (hf : (G.clusterPeaks ω x).Finite) :
    G.peakReturn ω x = ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
  rw [peakReturn,ite_eq_left hp,hf.encard_eq_coe,ENat.toENNReal_coe]
  rfl

lemma peakReturn_le_one (ω : Set E) (x : V) : G.peakReturn ω x ≤ 1 := by
  unfold peakReturn
  split_ifs with hp
  · apply ENNReal.inv_le_one.mpr
    have hh : (1 : ℕ∞) ≤ (G.clusterPeaks ω x).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨x,SimpleGraph.Reachable.refl x,hp⟩
    exact_mod_cast hh
  · exact zero_le

lemma peakRatioTransport_incoming_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (y : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      G.peakReturn ω y := by
  filter_upwards [G.no_heavy_finite_peaks_ae hc hl hq p] with ω hω
  rw [G.peakRatioTransport_incoming]
  by_cases hp : G.clusterPeak ω y
  · by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · have hi : (G.clusterPeaks ω y).Infinite := by
        intro hf
        exact hω y hf.toFinset.card ⟨hm,⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hp⟩
      simp [peakReturn,hp,hm,hi.encard_eq]
    · rw [ite_eq_left ⟨hp,hm⟩,G.peakReturn_eq_inv_ncard ω y hp
        (G.clusterPeaks_finite_of_mass_ne_top hc hl ω y hm)]
  · simp only [hp,false_and,ite_false,peakReturn]

theorem expected_clusterPeakRatio [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.clusterPeakRatio ω x ∂G.law p) =
    ∑ x ∈ (G.orbitRepresentatives hq).roots, ∫⁻ ω, G.peakReturn ω x ∂G.law p := by
  rw [show (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.clusterPeakRatio ω x ∂G.law p) = _ from
    OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
      G.peakRatioTransport G.measurable_peakRatioTransport G.peakRatioTransport_aut]
  apply Finset.sum_congr rfl
  intro x _
  exact lintegral_congr_ae (G.peakRatioTransport_incoming_ae hc hl hq p x)

lemma clusterPeak_of_subset {ω τ : Set E} (h : ω⊆τ) {x : V}
    (hp : G.clusterPeak τ x) : G.clusterPeak ω x :=
  fun y hy => hp y (hy.mono (G.openGraph_mono h))

lemma eventually_cluster_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.cluster ω x) :
    ∀ᶠ n in atTop, y∈G.cluster (a n) x := by
  obtain ⟨S,hS,hSω,hSy⟩ := G.mem_cluster_finite_witness hy
  have h : ∀ e∈S, ∀ᶠ n in atTop, e∈a n := by
    intro e he
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ hSω he)
    exact eventually_atTop.mpr ⟨n,fun m hm => ha hm hn⟩
  filter_upwards [(Filter.eventually_all_finite hS).mpr h] with n hn
  exact G.cluster_mono hn x hSy

lemma eventually_peaks_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.clusterPeaks ω x) :
    ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x := by
  filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy.1] with n hn
  refine ⟨hn,G.clusterPeak_of_subset ?_ hy.2⟩
  exact hu ▸ Set.subset_iUnion a n

lemma tendsto_peakCount_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (hi : (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => ((G.clusterPeaks (a n) x).encard : ℝ≥0∞)) atTop (𝓝 ∞) := by
  apply ENNReal.tendsto_nhds_top_iff_nat.mpr
  intro N
  obtain ⟨S,hS,hcard⟩ := hi.exists_subset_card_eq (N+1)
  have he : ∀ y∈(S : Set V), ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x :=
    fun y hy => G.eventually_peaks_of_exhaustion a ω ha hu (hS hy)
  filter_upwards [(Filter.eventually_all_finite S.finite_toSet).mpr he] with n hn
  have hh := ENat.toENNReal_mono (Set.encard_mono hn)
  have hb : ((N+1 : ℕ) : ℝ≥0∞) ≤ ((G.clusterPeaks (a n) x).encard : ℝ≥0∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe,hcard] using hh
  have hN : (N : ℝ≥0∞) < ((N+1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self N
  exact hN.trans_le hb

lemma tendsto_peakReturn_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (h : ¬ G.clusterPeak ω x ∨ (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => G.peakReturn (a n) x) atTop (𝓝 0) := by
  rcases h with hp|hi
  · have hw : ∃ y, (G.openGraph ω).Reachable x y ∧ ¬G.stabilizerWeight x y ≤ 1 := by
      obtain ⟨y,hy⟩ := not_forall.mp hp
      exact ⟨y,Classical.not_imp.mp hy⟩
    obtain ⟨y,hy,hyw⟩ := hw
    have he : ∀ᶠ n in atTop, G.peakReturn (a n) x = 0 := by
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      exact ite_eq_right (fun hh => hyw (hh y hn))
    exact tendsto_const_nhds.congr' (he.mono (fun _ hh => hh.symm))
  · have ht := (G.tendsto_peakCount_of_exhaustion a ω ha hu x hi).inv
    simp only [ENNReal.inv_top] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall (fun _ => zero_le))
    apply Eventually.of_forall
    intro n
    unfold peakReturn
    split_ifs
    · rfl
    · exact zero_le

end CriticalPercolation.BondGraph
end
end

end OAI
