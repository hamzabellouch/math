import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Modular.ModularIncidence
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def centeredCoefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e∈ω then 1-p else -p

def weightedIncidenceTerm (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈G.incidentEdges (G.cluster ω x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def weightedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.weightedIncidenceTerm p ω x e

lemma abs_centeredCoefficient_le_one (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (e : E) :
    |centeredCoefficient p ω e|≤1 := by
  unfold centeredCoefficient
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hp.1,hp.2]

lemma norm_weightedIncidenceTerm_le (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) (e : E) :
    ‖G.weightedIncidenceTerm p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold weightedIncidenceTerm
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · simp

lemma summable_weightedIncidence_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
    (G.weighted_incidence_le hc hl D K hD hK x _)

lemma summable_weightedIncidenceTerm (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (G.weightedIncidenceTerm p ω x) :=
  (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm).of_norm_bounded
    (G.norm_weightedIncidenceTerm_le p hp ω x)

lemma abs_weightedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    |G.weightedDiscrepancy p ω x| ≤ (D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal := by
  have hs := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
  calc
    _ ≤ ∑' e, (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal :=
      tsum_of_norm_bounded hs.hasSum (G.norm_weightedIncidenceTerm_le p hp ω x)
    _ = (∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro e
      split_ifs
      · exact G.bondWeight_ne_top x e
      · exact ENNReal.zero_ne_top
    _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
        (G.weighted_incidence_le hc hl D K hD hK x _)
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_natCast]

lemma measurable_weightedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.weightedDiscrepancy p ω x) := by
  apply Measurable.tsum
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  apply Measurable.ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf
    _ measurable_const
  exact measurable_const.mul (measurable_const.ite (measurable_set_mem e).setOf measurable_const)

lemma weightedIncidenceTerm_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) (e : E) :
    G.weightedIncidenceTerm p ω x e =
      (G.stabilizerWeight x y).toReal*G.weightedIncidenceTerm p ω y e := by
  unfold weightedIncidenceTerm
  rw [G.cluster_eq_of_reachable h,G.bondWeight_change_base hc hl x y,ENNReal.toReal_mul]
  split_ifs <;> ring

lemma weightedDiscrepancy_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : ℝ) (ω : Set E) (x y : V) (h : (G.openGraph ω).Reachable x y) :
    G.weightedDiscrepancy p ω x = (G.stabilizerWeight x y).toReal*G.weightedDiscrepancy p ω y := by
  unfold weightedDiscrepancy
  simp only [G.weightedIncidenceTerm_change_base hc hl p ω x y h,tsum_mul_left]

end CriticalPercolation.BondGraph
end
end

end OAI
