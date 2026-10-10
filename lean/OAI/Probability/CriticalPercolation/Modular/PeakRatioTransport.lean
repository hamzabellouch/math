import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Modular.ModularSuperlevels

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma one_le_modularClusterMass (ω : Set E) (x : V) :
    1 ≤ G.modularMass x (G.cluster ω x) := by
  have h := ENNReal.le_tsum (f := fun y => if y∈G.cluster ω x then G.stabilizerWeight x y else 0) x
  have hx : x∈G.cluster ω x := SimpleGraph.Reachable.refl x
  simpa only [modularMass,ite_eq_left hx,G.stabilizerWeight_self] using h

lemma stabilizerWeight_eq_one_of_peaks (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (hr : (G.openGraph ω).Reachable x y)
    (hx : G.clusterPeak ω x) (hy : G.clusterPeak ω y) :
    G.stabilizerWeight x y = 1 := by
  apply le_antisymm (hx y hr)
  have h := (G.stabilizerWeight_le_one_iff hc hl x y x).mp (hy x hr.symm)
  simpa only [G.stabilizerWeight_self] using h

def peakRatioTransport (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y∈G.clusterPeaks ω x then
    (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹
  else 0

def clusterPeakRatio (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.peakRatioTransport ω x y

lemma measurable_peakRatioTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω : Set E => G.peakRatioTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.mul (G.measurable_modularClusterMass y x).inv
  apply Measurable.inv
  apply Measurable.of_discrete.comp
  apply measurable_ncard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakRatioTransport_aut (φ : G.Aut) (ω : Set E) (x y : V) :
    G.peakRatioTransport (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.peakRatioTransport ω x y := by
  unfold peakRatioTransport
  rw [←φ.cluster_image,φ.modularMass_image,←φ.clusterPeaks_image,
    Set.ncard_image_of_injective _ φ.vertex.injective]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma clusterPeakRatio_eq_zero_of_heavy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hh : G.modularMass x (G.cluster ω x) = ∞) :
    G.clusterPeakRatio ω x = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro y
  unfold peakRatioTransport
  split_ifs
  · have hy : G.modularMass y (G.cluster ω x) = ∞ :=
      (G.modularMass_eq_top_change_base hc hl x y _).mp hh
    simp [hy]
  · rfl

lemma clusterPeakRatio_eq_inv_mass (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x y : V) (hh : G.modularMass x (G.cluster ω x) ≠ ∞)
    (hy : y∈G.clusterPeaks ω x) :
    G.clusterPeakRatio ω x = (G.modularMass y (G.cluster ω x))⁻¹ := by
  have hf := G.clusterPeaks_finite_of_mass_ne_top hc hl ω x hh
  have hnon := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hh
  have hpos : (G.clusterPeaks ω x).ncard ≠ 0 := (Set.ncard_pos hf).mpr hnon |>.ne'
  unfold clusterPeakRatio
  rw [tsum_eq_sum (s := hf.toFinset) (fun z hz => by
    simp only [hf.mem_toFinset] at hz
    simp only [peakRatioTransport,ite_eq_right hz])]
  have heq (z : V) (hz : z ∈ hf.toFinset) : G.peakRatioTransport ω x z =
      (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
    have hz' := hf.mem_toFinset.mp hz
    rw [peakRatioTransport,ite_eq_left hz',G.modularMass_change_base hc hl z y,
      G.stabilizerWeight_eq_one_of_peaks hc hl ω (hz'.1.symm.trans hy.1) hz'.2 hy.2,one_mul]
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
  rw [←mul_assoc,mul_comm ((G.clusterPeaks ω x).ncard : ℝ≥0∞),mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hpos) (ENNReal.natCast_ne_top _),mul_one]

lemma clusterPeakRatio_le_one (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) : G.clusterPeakRatio ω x ≤ 1 := by
  by_cases hh : G.modularMass x (G.cluster ω x) = ∞
  · rw [G.clusterPeakRatio_eq_zero_of_heavy hc hl ω x hh]
    exact zero_le
  · obtain ⟨y,hy⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hh
    rw [G.clusterPeakRatio_eq_inv_mass hc hl ω x y hh hy,
      G.cluster_eq_of_reachable hy.1]
    exact (ENNReal.inv_le_one).mpr (G.one_le_modularClusterMass ω y)

lemma peakRatioTransport_incoming (ω : Set E) (y : V) :
    (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      if G.clusterPeak ω y ∧ G.modularMass y (G.cluster ω y) ≠ ∞ then
        ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hp : G.clusterPeak ω y
  · have heq : (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
        ((G.modularMass y (G.cluster ω y))⁻¹ * ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹) *
          G.modularMass y (G.cluster ω y) := by
      conv_rhs => rhs; unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      by_cases hx : x∈G.cluster ω y
      · rw [ite_eq_left hx,peakRatioTransport,ite_eq_left ⟨hx.symm,hp⟩,
          G.cluster_eq_of_reachable hx.symm,G.clusterPeaks_eq_of_reachable hx.symm]
      · have hnot : y∉G.clusterPeaks ω x := fun h => hx h.1.symm
        simp only [peakRatioTransport,ite_eq_right hnot,zero_mul,ite_eq_right hx,mul_zero]
    rw [heq]
    by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · simp [hp,hm]
    · rw [ite_eq_left ⟨hp,hm⟩,mul_right_comm,
        ENNReal.inv_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm,
        one_mul]
  · have hz : ∀ x, G.peakRatioTransport ω x y = 0 := by
      intro x
      exact ite_eq_right (fun h => hp h.2)
    simp only [hz,zero_mul,tsum_zero,hp,false_and,ite_false]

end CriticalPercolation.BondGraph
end
end

end OAI
