import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.GeometricFourth
import OAI.Probability.CriticalPercolation.Modular.NormalizedDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.PeakVolumeBand
import OAI.Probability.CriticalPercolation.Modular.WeightedPeakBand

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma expected_peakBand_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) (T U : ℝ) (hT : 0<T)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p) ≤
      ENNReal.ofReal ((G.orbitRepresentatives hq).roots.card/T) := by
  rw [ENNReal.ofReal_div_of_pos hT,ENNReal.ofReal_natCast]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hT).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  apply le_trans _ (G.expected_peakVolumeBand_mul_le hc hl hq p (ENNReal.ofReal T) (ENNReal.ofReal U))
  apply mul_le_mul_right
  exact Finset.single_le_sum (f := fun y => ∫⁻ ω,
    G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω y ∂G.law p)
    (fun _ _ => zero_le) hx

lemma expected_discrepancy_peakBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal ((16:ℝ)^n)) (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  let C : ℝ := (D*(2*K)^2 : ℕ)
  let N : ℝ := (G.orbitRepresentatives hq).roots.card
  have ht : (0:ℝ)<16^n := by positivity
  have h4 := G.expected_discrepancy_peakBand_fourth hc hl D K hD hK p
    ((16:ℝ)^n) ((16:ℝ)^(n+1)) ht (by positivity) x
  apply geometric_fourth_bound _ (5*(C*16)^2*N^3) (by dsimp [N]; positivity) n
  apply h4.trans
  calc
    _ ≤ ENNReal.ofReal (5*(C*(16:ℝ)^(n+1))^2)*
        (ENNReal.ofReal (N/(16:ℝ)^n))^3 := by
          apply mul_le_mul_right
          exact ENNReal.pow_le_pow_left (G.expected_peakBand_le hc hl hq p _ _ ht x hx)
    _ = ENNReal.ofReal ((5*(C*16)^2*N^3)/(16:ℝ)^n) := by
      rw [←ENNReal.ofReal_pow (by dsimp [N]; positivity),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_succ]
      field_simp
      ring

lemma expected_discrepancyBand_geometric (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (n : ℕ) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
      G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^n))
        (ENNReal.ofReal ((16:ℝ)^(n+1))) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
  rw [G.expected_discrepancyBand_peak hc hl hq p _ _ (ENNReal.ofReal_pos.mpr (by positivity))]
  calc _ ≤ ∑ x∈(G.orbitRepresentatives hq).roots,
      ENNReal.ofReal ((5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (1/2:ℝ)^n) := by
          exact Finset.sum_le_sum (fun x hx => G.expected_discrepancy_peakBand_geometric hc hl hq D K hD hK p n x hx)
       _ = _ := by simp [nsmul_eq_mul]

end CriticalPercolation.BondGraph
end
end

end OAI
