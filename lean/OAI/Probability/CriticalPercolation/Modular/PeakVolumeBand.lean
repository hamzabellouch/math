import Mathlib
import OAI.Probability.CriticalPercolation.Modular.PeakReturn
import OAI.Probability.CriticalPercolation.Modular.WeightedPeakTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def peakVolumeBand (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.peakReturn ω x else 0

lemma measurable_peakVolumeBand [Countable V] [Countable E] (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.peakVolumeBand T U ω x) := by
  unfold peakVolumeBand
  exact (G.measurable_peakReturn x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

lemma peakVolumeBand_le_one (T U : ℝ≥0∞) (ω : Set E) (x : V) : G.peakVolumeBand T U ω x≤1 := by
  unfold peakVolumeBand
  split_ifs
  · exact G.peakReturn_le_one ω x
  · exact zero_le

lemma peakVolumeBand_support (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) (h : G.peakVolumeBand T U ω x≠0) :
    G.clusterPeak ω x ∧ T≤G.modularMass x (G.cluster ω x) ∧
      G.modularMass x (G.cluster ω x)<U := by
  have hb : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U := by
    by_contra hn
    exact h (ite_eq_right hn)
  have hp : G.clusterPeak ω x := by
    by_contra hn
    exact h (by simp only [peakVolumeBand,ite_eq_left hb,peakReturn,ite_eq_right hn])
  have hm : G.modularMass x (G.cluster ω x)≠∞ := by
    intro he
    have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
    have hvol : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
    rw [hvol] at hb
    exact (not_le.mpr hT) hb.1
  rw [G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm] at hb
  exact ⟨hp,hb⟩

lemma peakVolumeBand_mul_le (T U : ℝ≥0∞) (ω : Set E) (x : V) :
    T*G.peakVolumeBand T U ω x ≤ G.normalizedClusterVolume ω x*G.peakReturn ω x := by
  unfold peakVolumeBand
  split_ifs with h
  · gcongr
    exact h.1
  · simp

theorem expected_peakVolumeBand_mul_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) :
    T*(∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.peakVolumeBand T U ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card := by
  calc _ = ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, T*G.peakVolumeBand T U ω x ∂G.law p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        exact (lintegral_const_mul'' T (G.measurable_peakVolumeBand T U x).aemeasurable).symm
       _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
          ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p := by
        apply Finset.sum_le_sum
        intro x _
        exact lintegral_mono (fun ω => G.peakVolumeBand_mul_le T U ω x)
       _ ≤ _ := G.expected_peak_volume_le hc hl hq p

end CriticalPercolation.BondGraph
end
end

end OAI
