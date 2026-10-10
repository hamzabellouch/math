import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness
import OAI.Probability.CriticalPercolation.ProductMeasure.SusceptibilityMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma small_parameter_tail_bound (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1)
    (u : V) (s : ℕ) : (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let K := G.inducedBallExhaustion hconnected hlocal u
  have ht := BernoulliProduct.tendsto_real_finiteWitness p (G.clusterTail u s)
    (G.clusterTail_isUpperSet u s) (G.clusterTail_hasFiniteOpenWitness u s) K
  have ht' : Tendsto (fun n => (s:ℝ)*(G.law p).real {ω | K n ∩ ω ∈ G.clusterTail u s})
      atTop (𝓝 ((s:ℝ)*(G.law p).real (G.clusterTail u s))) := by
    simpa only [law,← BernoulliProduct.law_const] using ht.const_mul (s:ℝ)
  apply le_of_tendsto ht'
  exact Filter.Eventually.of_forall (fun n => G.induced_clusterTail_measure_bound hlocal p D hD hpD
    (G.vertexBall u n) (G.vertexBall_finite hlocal u n) ⟨u,G.mem_vertexBall_self u n⟩ s)

lemma small_parameter_infinite_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) (u : V) :
    G.law p (G.infiniteEvent u) = 0 := by
  have hreal : (G.law p).real (G.infiniteEvent u) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! hp
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(G.law p).real (G.infiniteEvent u))
    have hh : (n:ℝ)*(G.law p).real (G.infiniteEvent u) ≤ 2 := by
      calc
        _ ≤ (n:ℝ)*(G.law p).real (G.clusterTail u n) :=
          mul_le_mul_of_nonneg_left (measureReal_mono (G.infiniteEvent_subset_clusterTail u n))
            (Nat.cast_nonneg _)
        _ ≤ 2 := G.small_parameter_tail_bound hconnected hlocal p D hD hpD u n
    have hlt := (div_lt_iff₀ hp).mp hn
    linarith
  have hh := (ENNReal.toReal_eq_zero_iff _).mp hreal
  exact hh.resolve_right (measure_ne_top _ _)

lemma small_parameter_percolates_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) :
    G.law p G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  apply (G.percolates_null_iff (G.law p)).mpr
  exact G.small_parameter_infinite_null hconnected hlocal p D hD hpD

theorem criticalProbability_pos (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
    (0:ℝ)<G.criticalProbability := by
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  have hd : (0:ℝ)<4*(D:ℝ)+1 := by positivity
  let p₀ : unitInterval := ⟨1/(4*(D:ℝ)+1), by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by
        have hh : (0:ℝ) ≤ 4 * (D:ℝ) := by positivity
        linarith)⟩
  have he : (p₀:ℝ)*(4*(D:ℝ)+1)=1 := div_mul_cancel₀ _ hd.ne'
  have hp₀ : (0:ℝ)<p₀ := one_div_pos.mpr hd
  have hsmall : ∀ p : unitInterval, p≤p₀ → 4*(p:ℝ)*D≤1 := by
    intro p hp
    have hn : (0:ℝ)≤D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (show (p:ℝ)≤p₀ from hp) hn
    nlinarith [p₀.property.1]
  have hle : p₀≤G.criticalProbability := by
    apply le_sInf
    intro p hp
    by_contra h
    have hpp : p≤p₀ := (not_le.mp h).le
    have hz := G.small_parameter_percolates_null hconnected hlocal p D hD (hsmall p hpp)
    exact (ne_of_gt hp) hz
  exact hp₀.trans_le hle

end CriticalPercolation.BondGraph
end
end
end

end OAI
