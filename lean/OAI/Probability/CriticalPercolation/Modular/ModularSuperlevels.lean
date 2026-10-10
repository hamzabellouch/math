import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Modular.PeakClusters

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_le_one_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight a x ≤ 1 ↔ G.stabilizerWeight o x ≤ G.stabilizerWeight o a := by
  rw [G.stabilizerWeight_change_base hc hl o a x]
  conv_rhs => rhs; rw [←mul_one (G.stabilizerWeight o a)]
  exact (ENNReal.mul_le_mul_iff_right (G.stabilizerWeight_pos hc hl o a).ne'
    (G.stabilizerWeight_ne_top o a)).symm

def clusterUpperSet (ω : Set E) (v : V) : Set V :=
  {x | x ∈ G.cluster ω v ∧ 1 ≤ G.stabilizerWeight v x}

lemma mem_clusterUpperSet_self (ω : Set E) (v : V) : v∈G.clusterUpperSet ω v := by
  exact ⟨SimpleGraph.Reachable.refl v,by simp⟩

lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (ε := 1) one_ne_zero).subset
  intro x hx
  change 1 ≤ if x∈G.cluster ω v then G.stabilizerWeight v x else 0
  rw [ite_eq_left hx.1]
  exact hx.2

lemma finite_clusterUpperSet_has_peak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hf : (G.clusterUpperSet ω v).Finite) :
    ∃ y∈G.cluster ω v, G.clusterPeak ω y ∧
      G.peakBound hf.toFinset.card ω y := by
  obtain ⟨y,hy,hmax⟩ := hf.toFinset.exists_max_image (G.stabilizerWeight v)
    ⟨v,hf.mem_toFinset.mpr (G.mem_clusterUpperSet_self ω v)⟩
  have hy' := hf.mem_toFinset.mp hy
  have hbound (z : V) (hz : z∈G.cluster ω v) : G.stabilizerWeight v z ≤ G.stabilizerWeight v y := by
    by_cases h : 1≤G.stabilizerWeight v z
    · exact hmax z (hf.mem_toFinset.mpr ⟨hz,h⟩)
    · exact (le_of_not_ge h).trans hy'.2
  have hpeak : G.clusterPeak ω y := by
    intro z hz
    exact (G.stabilizerWeight_le_one_iff hc hl v y z).mpr (hbound z (hy'.1.trans hz))
  refine ⟨y,hy'.1,hpeak,hf.toFinset,le_rfl,?_⟩
  intro z hz
  apply hf.mem_toFinset.mpr
  refine ⟨hy'.1.trans hz.1,?_⟩
  exact hy'.2.trans ((G.stabilizerWeight_le_one_iff hc hl v z y).mp (hz.2 y hz.1.symm))

lemma clusterPeaks_finite_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Finite := by
  apply (G.finite_clusterUpperSet_of_mass_ne_top hm).subset
  intro x hx
  refine ⟨hx.1,?_⟩
  have hh := (G.stabilizerWeight_le_one_iff hc hl v x v).mp (hx.2 v hx.1.symm)
  simpa only [G.stabilizerWeight_self] using hh

lemma clusterPeaks_nonempty_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Nonempty := by
  obtain ⟨y,hy,hp,_⟩ := G.finite_clusterUpperSet_has_peak hc hl ω v
    (G.finite_clusterUpperSet_of_mass_ne_top hm)
  exact ⟨y,hy,hp⟩

end CriticalPercolation.BondGraph
end
end

end OAI
