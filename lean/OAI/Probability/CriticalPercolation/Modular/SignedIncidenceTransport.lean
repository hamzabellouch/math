import Mathlib
import OAI.Probability.CriticalPercolation.Modular.SignedDiscrepancyContinuity
import OAI.Probability.CriticalPercolation.Modular.NormalizedIncidenceTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma normalizedSelectedIncidence_toReal (H : Set E → E → ℝ≥0∞)
    (hH : ∀ ω e, H ω e≠∞) (ω : Set E) (x : V) :
    (G.normalizedSelectedIncidence H ω x).toReal =
      (∑' e, if e∈G.incidentEdges (G.cluster ω x) then
        (H ω e).toReal*(G.bondWeight x e).toReal else 0)*(G.reciprocalClusterMass ω x).toReal := by
  unfold normalizedSelectedIncidence
  rw [ENNReal.toReal_mul,ENNReal.tsum_toReal_eq]
  · congr 1
    apply tsum_congr
    intro e
    split_ifs <;> simp only [ENNReal.toReal_mul,ENNReal.toReal_zero]
  · intro e
    split_ifs
    · exact ENNReal.mul_ne_top (hH ω e) (G.bondWeight_ne_top x e)
    · exact ENNReal.zero_ne_top

lemma normalizedSignedDiscrepancy_eq_selected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (ω : Set E) (x : V) :
    G.normalizedSignedDiscrepancy p ω x =
      (G.normalizedSelectedIncidence (fun ω e => if e∈ω then 1 else 0) ω x).toReal -
        p*(G.normalizedSelectedIncidence (fun _ _ => 1) ω x).toReal := by
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [G.normalizedSignedDiscrepancy_heavy p ω x hm,normalizedSelectedIncidence,reciprocalClusterMass,hm]
  · let A := fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal
    have hAs : Summable A := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
    let B := fun e => if e∈ω then A e else 0
    have hBs : Summable B := hAs.indicator (fun e => e∈ω)
    have he (e : E) : G.weightedIncidenceTerm p ω x e=B e-p*A e := by
      by_cases hi : e∈G.incidentEdges (G.cluster ω x) <;> by_cases ho : e∈ω <;>
        simp [weightedIncidenceTerm,centeredCoefficient,A,B,hi,ho] <;> ring
    have hdisc : G.weightedDiscrepancy p ω x=(∑' e, B e)-p*(∑' e, A e) := by
      simp_rw [weightedDiscrepancy,he]
      rw [hBs.tsum_sub (hAs.mul_left p),tsum_mul_left]
    rw [G.normalizedSelectedIncidence_toReal _ (fun _ _ => by
        split_ifs
        · exact ENNReal.one_ne_top
        · exact ENNReal.zero_ne_top),
      G.normalizedSelectedIncidence_toReal _ (fun _ _ => ENNReal.one_ne_top)]
    have hAeq : (fun e => if e∈G.incidentEdges (G.cluster ω x) then
        (1:ℝ≥0∞).toReal*(G.bondWeight x e).toReal else 0)=A := by
      funext e
      by_cases he : e∈G.incidentEdges (G.cluster ω x) <;> simp [A,he]
    have hBeq : (fun e => if e∈G.incidentEdges (G.cluster ω x) then
        (if e∈ω then (1:ℝ≥0∞) else 0).toReal*(G.bondWeight x e).toReal else 0)=B := by
      funext e
      by_cases hi : e∈G.incidentEdges (G.cluster ω x) <;> by_cases ho : e∈ω <;> simp [A,B,hi,ho]
    rw [hAeq,hBeq,normalizedSignedDiscrepancy,hdisc,reciprocalClusterMass,ENNReal.toReal_inv]
    ring

lemma integrable_selectedIncidence_toReal [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1) (x : V) :
    Integrable (fun ω => (G.normalizedSelectedIncidence H ω x).toReal) (G.law p) := by
  apply Integrable.of_bound ((G.measurable_normalizedSelectedIncidence H hm x).ennreal_toReal.aestronglyMeasurable)
    (D*(2*K) : ℕ)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (G.normalizedSelectedIncidence_le hc hl D K hD hK H hH ω x)).trans_eq
    (ENNReal.toReal_natCast _)

end CriticalPercolation.BondGraph
end
end

end OAI
