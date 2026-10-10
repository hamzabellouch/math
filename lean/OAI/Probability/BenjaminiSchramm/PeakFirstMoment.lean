import OAI.Probability.BenjaminiSchramm.PeakLayerEstimate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def normalizedPeakTransport (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ G.clusterPeaks ω x then ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹ else 0

lemma normalizedPeakTransport_aut (φ : G.Aut) (ω : Set E) (x y : V) :
    G.normalizedPeakTransport (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.normalizedPeakTransport ω x y := by
  unfold normalizedPeakTransport
  rw [← φ.clusterPeaks_image, φ.vertex.injective.encard_image]
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]

lemma measurable_normalizedPeakTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω => G.normalizedPeakTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.inv
  apply (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
  apply measurable_encard.comp
  exact Measurable.of_eval (fun z => G.measurable_mem_clusterPeaks x z)

lemma normalizedPeakTransport_outgoing (ω : Set E) (x : V) :
    (∑' y, G.normalizedPeakTransport ω x y) ≤ 1 := by
  have he : (∑' y, G.normalizedPeakTransport ω x y) =
      ∑' _y : G.clusterPeaks ω x, ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹ := by
    rw [tsum_subtype (G.clusterPeaks ω x)
      (fun _ : V => ((G.clusterPeaks ω x).encard : ℝ≥0∞)⁻¹)]
    rfl
  rw [he, ENNReal.tsum_set_const]
  exact ENNReal.mul_inv_le_one _

lemma normalizedPeakTransport_incoming (ω : Set E) (y : V) :
    (∑' x, G.normalizedPeakTransport ω x y * G.stabilizerWeight y x) =
      G.peakReturn ω y * G.modularMass y (G.cluster ω y) := by
  by_cases hp : G.clusterPeak ω y
  · rw [peakReturn, ite_eq_left hp, modularMass, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ G.cluster ω y
    · have hxy : y ∈ G.clusterPeaks ω x := ⟨hx.symm,hp⟩
      rw [normalizedPeakTransport, ite_eq_left hxy, ite_eq_left hx,
        G.clusterPeaks_eq_of_reachable hx.symm]
    · have hxy : y ∉ G.clusterPeaks ω x := fun hh => hx hh.1.symm
      simp only [normalizedPeakTransport, ite_eq_right hxy, ite_eq_right hx,
        zero_mul, mul_zero]
  · rw [peakReturn, ite_eq_right hp, zero_mul]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    have hxy : y ∉ G.clusterPeaks ω x := fun hh => hp hh.2
    simp only [normalizedPeakTransport, ite_eq_right hxy, zero_mul]

lemma normalizedPeakTransport_eq_reverse (ω : Set E) (x y : V) :
    G.normalizedPeakTransport ω x y =
      if x ∈ G.cluster ω y then G.peakReturn ω y else 0 := by
  by_cases hp : G.clusterPeak ω y
  · by_cases hx : x ∈ G.cluster ω y
    · have hxy : y ∈ G.clusterPeaks ω x := ⟨hx.symm,hp⟩
      rw [normalizedPeakTransport, ite_eq_left hxy, ite_eq_left hx, peakReturn,
        ite_eq_left hp, G.clusterPeaks_eq_of_reachable hx.symm]
    · have hxy : y ∉ G.clusterPeaks ω x := fun hh => hx hh.1.symm
      simp only [normalizedPeakTransport, ite_eq_right hxy, ite_eq_right hx]
  · have hxy : y ∉ G.clusterPeaks ω x := fun hh => hp hh.2
    simp only [normalizedPeakTransport, ite_eq_right hxy, peakReturn, ite_eq_right hp,
      ite_self]

theorem expected_peakReturn_modularMass_sum [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.peakReturn ω x * G.modularMass x (G.cluster ω x) ∂G.law p) ≤
        ((G.orbitRepresentatives hq).roots.card : ℝ≥0∞) := by
  rw [← show (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, ∑' y, G.normalizedPeakTransport ω x y ∂G.law p) =
      ∑ y ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, G.peakReturn ω y * G.modularMass y (G.cluster ω y) ∂G.law p from by
    rw [OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
      G.normalizedPeakTransport G.measurable_normalizedPeakTransport G.normalizedPeakTransport_aut]
    simp_rw [G.normalizedPeakTransport_incoming]]
  calc
    _ ≤ ∑ _x ∈ (G.orbitRepresentatives hq).roots, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro x _
      exact (lintegral_mono fun ω => G.normalizedPeakTransport_outgoing ω x).trans_eq
        (by simp)
    _ = _ := by simp

end CriticalPercolation.BondGraph

end

end OAI
