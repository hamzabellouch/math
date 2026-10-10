import Mathlib
import OAI.Probability.CriticalPercolation.Modular.RandomTiltedTransport
import OAI.Probability.CriticalPercolation.Modular.PeakClusters
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def heavyPeakTransport (N : ℕ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧ y∈G.clusterPeaks ω x then 1 else 0

lemma measurable_heavyPeakTransport (N : ℕ) (x y : V) :
    Measurable (fun ω : Set E => G.heavyPeakTransport N ω x y) := by
  apply measurable_const.ite _ measurable_const
  exact (G.measurableSet_heavyClusterEvent x x).inter
    ((G.measurable_peakBound N x).and (G.measurable_mem_clusterPeaks x y)).setOf

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.heavyPeakTransport N (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.heavyPeakTransport N ω x y := by
  unfold heavyPeakTransport
  rw [←φ.cluster_image,φ.modularMass_image,φ.peakBound_iff,←φ.clusterPeaks_image]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_out_bound (N : ℕ) (ω : Set E) (x : V) :
    (∑' y, G.heavyPeakTransport N ω x y) ≤ N := by
  by_cases hb : G.peakBound N ω x
  · obtain ⟨S,hS,hcover⟩ := hb
    calc
      _ ≤ ∑' y, if y∈S then (1 : ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro y
        unfold heavyPeakTransport
        split_ifs with hh hs
        · rfl
        · exact False.elim (hs (hcover hh.2.2))
        · exact zero_le
        · rfl
      _ = (S.card : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        calc
          _ = ∑ y ∈ S, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun y hy => ite_eq_left hy)
          _ = _ := by simp
      _ ≤ N := by exact_mod_cast hS
  · simp only [heavyPeakTransport,hb,false_and,and_false,ite_false,tsum_zero,zero_le]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_infinite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (N : ℕ) (ω : Set E) (y : V)
    (hh : G.modularMass y (G.cluster ω y) = ∞) (hb : G.peakBound N ω y)
    (hp : G.clusterPeak ω y) :
    (∑' x, G.heavyPeakTransport N ω x y * G.stabilizerWeight y x) = ∞ := by
  apply top_unique
  rw [←hh]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ G.cluster ω y
  · have hxy : (G.openGraph ω).Reachable x y := hx.symm
    have he : G.cluster ω x = G.cluster ω y := G.cluster_eq_of_reachable hxy
    have hhx : G.modularMass x (G.cluster ω x) = ∞ := by
      rw [he,G.modularMass_eq_top_change_base hc hl x y]
      exact hh
    have hbx : G.peakBound N ω x := (G.peakBound_iff_of_reachable N hxy).mpr hb
    have hcond : G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧
        y∈G.clusterPeaks ω x := ⟨hhx,hbx,⟨hxy,hp⟩⟩
    simp only [ite_eq_left hx,heavyPeakTransport,ite_eq_left hcond,one_mul,le_refl]
  · simp only [ite_eq_right hx,zero_le]

lemma no_heavy_finite_peaks_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, ∀ y : V, ∀ N : ℕ,
      ¬ (G.modularMass y (G.cluster ω y) = ∞ ∧ G.peakBound N ω y ∧ G.clusterPeak ω y) := by
  apply ae_all_iff.mpr
  intro y
  apply ae_all_iff.mpr
  intro N
  have hfin := OrbitRepresentatives.incoming_finite_ae G (G.orbitRepresentatives hq)
    hc hl p (G.heavyPeakTransport N) (G.measurable_heavyPeakTransport N)
    (G.heavyPeakTransport_aut N) N (ENNReal.natCast_lt_top N) (G.heavyPeakTransport_out_bound N) y
  filter_upwards [hfin] with ω hω
  rintro ⟨hh,hb,hp⟩
  rw [G.heavyPeakTransport_infinite hc hl N ω y hh hb hp] at hω
  exact (lt_irrefl _ hω)

end CriticalPercolation.BondGraph
end
end

end OAI
