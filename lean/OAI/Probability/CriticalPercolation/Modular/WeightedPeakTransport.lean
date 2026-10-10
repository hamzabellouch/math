import Mathlib
import OAI.Probability.CriticalPercolation.Modular.RandomTiltedTransport
import OAI.Probability.CriticalPercolation.Modular.PeakRatioTransport
import OAI.Probability.CriticalPercolation.Modular.PeakReturn

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterPeakRatio_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeakRatio ω x=G.clusterPeakRatio ω y := by
  unfold clusterPeakRatio peakRatioTransport
  simp only [G.cluster_eq_of_reachable h,G.clusterPeaks_eq_of_reachable h]

lemma measurable_clusterPeakRatio [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeakRatio ω x) :=
  Measurable.tsum (fun y => G.measurable_peakRatioTransport x y)

lemma Aut.clusterPeakRatio (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeakRatio (φ.edge '' ω) (φ.vertex x)=G.clusterPeakRatio ω x := by
  unfold CriticalPercolation.BondGraph.clusterPeakRatio
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  exact G.peakRatioTransport_aut φ ω x y

lemma weighted_peakRatio_incoming (F : (Set E) → V → ℝ≥0∞)
    (hc : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y)
    (ω : Set E) (y : V) :
    (∑' x, (F ω x*G.peakRatioTransport ω x y)*G.stabilizerWeight y x) =
      F ω y*(∑' x, G.peakRatioTransport ω x y*G.stabilizerWeight y x) := by
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : y∈G.clusterPeaks ω x
  · rw [hc ω x y hx.1,mul_assoc]
  · simp only [peakRatioTransport,ite_eq_right hx,mul_zero,zero_mul]

theorem expected_weighted_peakRatio [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (F : (Set E) → V → ℝ≥0∞)
    (hm : ∀ x, Measurable (fun ω => F ω x))
    (ha : ∀ (φ : G.Aut) ω x, F (φ.edge '' ω) (φ.vertex x)=F ω x)
    (hr : ∀ ω x y, (G.openGraph ω).Reachable x y → F ω x=F ω y) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.clusterPeakRatio ω x ∂G.law p) =
    ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, F ω x*G.peakReturn ω x ∂G.law p := by
  have h := OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
    (fun ω x y => F ω x*G.peakRatioTransport ω x y)
    (fun x y => (hm x).mul (G.measurable_peakRatioTransport x y))
    (fun φ ω x y => by rw [ha φ ω x,G.peakRatioTransport_aut φ ω x y])
  simp only [ENNReal.tsum_mul_left,G.weighted_peakRatio_incoming F hr] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  apply lintegral_congr_ae
  filter_upwards [G.peakRatioTransport_incoming_ae hc hl hq p x] with ω hω
  rw [hω]

def normalizedClusterVolume (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.clusterPeakRatio ω x=0 then 0 else (G.clusterPeakRatio ω x)⁻¹

lemma measurable_normalizedClusterVolume [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.normalizedClusterVolume ω x) := by
  unfold normalizedClusterVolume
  exact measurable_const.ite
    (measurableSet_eq_fun (G.measurable_clusterPeakRatio x) measurable_const)
    (G.measurable_clusterPeakRatio x).inv

lemma Aut.normalizedClusterVolume (φ : G.Aut) (ω : Set E) (x : V) :
    G.normalizedClusterVolume (φ.edge '' ω) (φ.vertex x)=G.normalizedClusterVolume ω x := by
  unfold CriticalPercolation.BondGraph.normalizedClusterVolume
  rw [φ.clusterPeakRatio]

lemma normalizedClusterVolume_eq_of_reachable (ω : Set E) {x y : V}
    (h : (G.openGraph ω).Reachable x y) :
    G.normalizedClusterVolume ω x=G.normalizedClusterVolume ω y := by
  unfold normalizedClusterVolume
  rw [G.clusterPeakRatio_eq_of_reachable ω h]

lemma normalizedClusterVolume_eq_at_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) (hf : G.modularMass x (G.cluster ω x)≠∞) :
    G.normalizedClusterVolume ω x=G.modularMass x (G.cluster ω x) := by
  rw [normalizedClusterVolume,G.clusterPeakRatio_eq_inv_mass hc hl ω x x hf
    ⟨SimpleGraph.Reachable.refl x,hp⟩,ite_eq_right (ENNReal.inv_ne_zero.mpr hf),inv_inv]

lemma normalizedClusterVolume_mul_ratio_le (ω : Set E) (x : V) :
    G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x≤1 := by
  unfold normalizedClusterVolume
  split_ifs with h
  · simp
  · by_cases ht : G.clusterPeakRatio ω x=∞
    · simp [ht]
    · rw [ENNReal.inv_mul_cancel h ht]

theorem expected_peak_volume_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.normalizedClusterVolume ω x*G.peakReturn ω x ∂G.law p) ≤
    (G.orbitRepresentatives hq).roots.card := by
  rw [←G.expected_weighted_peakRatio hc hl hq p G.normalizedClusterVolume
    G.measurable_normalizedClusterVolume (fun φ => φ.normalizedClusterVolume)
    (fun ω _ _ h => G.normalizedClusterVolume_eq_of_reachable ω h)]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro x _
        calc _ ≤ ∫⁻ ω, (1 : ℝ≥0∞) ∂G.law p := lintegral_mono (fun ω =>
              G.normalizedClusterVolume_mul_ratio_le ω x)
             _ = 1 := by simp
       _ = _ := by simp

end CriticalPercolation.BondGraph
end
end

end OAI
