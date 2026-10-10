import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.PeakVolumeBand

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def normalizedAbsoluteDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ENNReal.ofReal |G.weightedDiscrepancy p ω x| / G.modularMass x (G.cluster ω x)

lemma measurable_normalizedAbsoluteDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedAbsoluteDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).norm.ennreal_ofReal.div
    (G.measurable_modularClusterMass x x)

lemma Aut.weightedDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.weightedDiscrepancy p (φ.edge '' ω) (φ.vertex x) = G.weightedDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.weightedDiscrepancy
  rw [←φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  rw [←φ.cluster_image]
  have hend (v : V) : φ.vertex v∈G.ends (φ.edge e) ↔ v∈G.ends e := by
    rw [φ.preserves]
    simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]
  have hi : φ.edge e∈G.incidentEdges (φ.vertex '' G.cluster ω x) ↔ e∈G.incidentEdges (G.cluster ω x) := by
    constructor
    · rintro ⟨z,⟨v,hv,rfl⟩,hz⟩
      exact ⟨v,hv,(hend v).mp hz⟩
    · rintro ⟨v,hv,hve⟩
      exact ⟨φ.vertex v,⟨v,hv,rfl⟩,(hend v).mpr hve⟩
  rw [hi]
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,φ.bondWeight]

lemma Aut.normalizedAbsoluteDiscrepancy (φ : G.Aut) (p : ℝ) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p (φ.edge '' ω) (φ.vertex x) =
      G.normalizedAbsoluteDiscrepancy p ω x := by
  unfold CriticalPercolation.BondGraph.normalizedAbsoluteDiscrepancy
  rw [φ.weightedDiscrepancy,←φ.cluster_image,φ.modularMass_image]

lemma normalizedAbsoluteDiscrepancy_eq_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable x y) :
    G.normalizedAbsoluteDiscrepancy p ω x = G.normalizedAbsoluteDiscrepancy p ω y := by
  unfold normalizedAbsoluteDiscrepancy
  rw [G.weightedDiscrepancy_change_base hc hl p ω x y h,abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg,ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (G.stabilizerWeight_ne_top x y),
    G.modularMass_change_base hc hl x y,G.cluster_eq_of_reachable h]
  exact ENNReal.mul_div_mul_left _ _ (G.stabilizerWeight_pos hc hl x y).ne'
    (G.stabilizerWeight_ne_top x y)

lemma normalizedAbsoluteDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤ (D*(2*K) : ℕ) := by
  unfold normalizedAbsoluteDiscrepancy
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [hm]
  · apply (ENNReal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).mpr
    calc _ ≤ ENNReal.ofReal ((D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal) :=
          ENNReal.ofReal_le_ofReal (G.abs_weightedDiscrepancy_le hc hl D K hD hK p hp ω x hm)
         _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_toReal hm]

def discrepancyVolumeBand (p : ℝ) (T U : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U then
    G.normalizedAbsoluteDiscrepancy p ω x else 0

lemma measurable_discrepancyVolumeBand [Countable V] [Countable E]
    (p : ℝ) (T U : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeBand p T U ω x) := by
  exact (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    ((measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)).inter
      (measurableSet_lt (G.measurable_normalizedClusterVolume x) measurable_const)) measurable_const

lemma band_volume_ratio (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.clusterPeakRatio ω x =
      G.discrepancyVolumeBand p T U ω x := by
  unfold discrepancyVolumeBand
  split_ifs with h
  · have hne : G.clusterPeakRatio ω x≠0 := by
      intro he
      have hz : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,he]
      rw [hz] at h
      exact (not_le.mpr hT) h.1
    rw [normalizedClusterVolume,ite_eq_right hne,mul_assoc,
      ENNReal.inv_mul_cancel hne (ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)),mul_one]
  · simp

lemma band_volume_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (T U : ℝ≥0∞) (hT : 0<T) (ω : Set E) (x : V) :
    (G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)*G.peakReturn ω x =
      ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x := by
  by_cases h : T≤G.normalizedClusterVolume ω x ∧ G.normalizedClusterVolume ω x<U
  · by_cases hp : G.clusterPeak ω x
    · have hm : G.modularMass x (G.cluster ω x)≠∞ := by
        intro he
        have hz := G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x he
        have hv : G.normalizedClusterVolume ω x=0 := by simp [normalizedClusterVolume,hz]
        rw [hv] at h
        exact (not_le.mpr hT) h.1
      rw [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,ite_eq_left h,
        G.normalizedClusterVolume_eq_at_peak hc hl ω x hp hm,normalizedAbsoluteDiscrepancy,
        ENNReal.div_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm]
    · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_left h,peakReturn,ite_eq_right hp,mul_zero]
  · simp only [discrepancyVolumeBand,peakVolumeBand,ite_eq_right h,zero_mul,mul_zero]

theorem expected_discrepancyBand_peak [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (T U : ℝ≥0∞) (hT : 0<T) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.discrepancyVolumeBand p T U ω x ∂G.law p) =
      ∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
        ENNReal.ofReal |G.weightedDiscrepancy p ω x| *G.peakVolumeBand T U ω x ∂G.law p := by
  have ht := G.expected_weighted_peakRatio hc hl hq p
    (fun ω x => G.discrepancyVolumeBand p T U ω x*G.normalizedClusterVolume ω x)
    (fun x => (G.measurable_discrepancyVolumeBand p T U x).mul (G.measurable_normalizedClusterVolume x))
    (fun φ ω x => by
      simp only [discrepancyVolumeBand,φ.normalizedClusterVolume,φ.normalizedAbsoluteDiscrepancy])
    (fun ω x y h => by
      simp only [discrepancyVolumeBand,G.normalizedClusterVolume_eq_of_reachable ω h,
        G.normalizedAbsoluteDiscrepancy_eq_of_reachable hc hl p ω h])
  simpa only [G.band_volume_ratio hc hl p T U hT,G.band_volume_peak hc hl p T U hT] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
