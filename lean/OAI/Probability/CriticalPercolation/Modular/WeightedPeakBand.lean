import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.IncidenceIdentity
import OAI.Probability.CriticalPercolation.Modular.WeightedQueryLaw
import OAI.Probability.CriticalPercolation.Modular.WeightedDiscrepancyLimit
import OAI.Probability.CriticalPercolation.Modular.WeightedExplorationCost
import OAI.Probability.CriticalPercolation.Modular.PeakVolumeBand
import OAI.Probability.CriticalPercolation.Criticality.FourthMomentFatou

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] in
lemma measurable_restrictedWeightedDiscrepancy (s : Set E) [Fintype s] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.restrictedWeightedDiscrepancy s p ω x) := by
  simp only [G.restrictedWeightedDiscrepancy_eq_tree]
  exact (measurable_of_finite (fun η : Set s =>
    (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
      (fun e : s => (G.bondWeight x e.val).toReal) p η)).comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))

theorem expected_discrepancy_peakBand_fourth (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval)
    (T U : ℝ) (hT : 0<T) (hU : 0≤U) (x : V) :
    (∫⁻ ω, ENNReal.ofReal |G.weightedDiscrepancy p ω x| *
      G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^4 ≤
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*U)^2)*
        (∫⁻ ω, G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x ∂G.law p)^3 := by
  classical
  let L := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let (n : ℕ) : Fintype (L n) := (L.finite n).fintype
  let h : Set E → ℝ≥0∞ := fun ω => G.peakVolumeBand (ENNReal.ofReal T) (ENNReal.ofReal U) ω x
  have hsupport (ω : Set E) (hh : h ω≠0) :=
    G.peakVolumeBand_support hc hl (ENNReal.ofReal T) (ENNReal.ofReal U)
      (ENNReal.ofReal_pos.mpr hT) ω x hh
  have hcost (n : ℕ) (ω : Set E) (hh : h ω≠0) :
      (IncidenceSearch.tree (G.restrictEdges (L n)) x).quadraticCost
        (fun e : L n => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
    let := (L.finite n).fintype
    exact G.restriction_quadratic_real_le hc hl D K hD hK (L n) ω x
      (hsupport ω hh).1 U hU (hsupport ω hh).2.2.le
  let f : ℕ → Set E → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal |G.restrictedWeightedDiscrepancy (L n) p ω x| * h ω
  apply lintegral_fourth_bound_of_tendsto (G.law p) f
    (fun ω => ENNReal.ofReal |G.weightedDiscrepancy p ω x| * h ω) _
  · intro n
    let := (L.finite n).fintype
    exact (G.measurable_restrictedWeightedDiscrepancy (L n) p x).norm.ennreal_ofReal.mul
      (G.measurable_peakVolumeBand _ _ x)
  · intro ω
    by_cases hh : h ω=0
    · simpa only [f,hh,mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
    · have hm : G.modularMass x (G.cluster ω x)≠∞ :=
        ne_top_of_lt ((hsupport ω hh).2.2.trans_le (le_top))
      exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal
        ((G.tendsto_restrictedWeightedDiscrepancy hc hl D K hD hK p p.2 L ω x hm).abs))
        (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (G.peakVolumeBand_le_one _ _ ω x)))
  · intro n
    let := (L.finite n).fintype
    have hn := @SearchTree.restricted_weighted_event_fourth E (IncidenceSearch.State (L n)) (L n) _ (Classical.decEq _)
      (fun e : L n => (G.bondWeight x e.val).toReal)
      (IncidenceSearch.tree (G.restrictEdges (L n)) x) (IncidenceSearch.tree_valid _ _) p
      ((D*(2*K)^2 : ℕ)*U) (by positivity) h (G.measurable_peakVolumeBand _ _ x)
      (fun ω => G.peakVolumeBand_le_one _ _ ω x) (hcost n)
    simpa only [f,G.restrictedWeightedDiscrepancy_eq_tree,BernoulliProduct.law_const,BondGraph.law] using hn

end CriticalPercolation.BondGraph
end
end

end OAI
