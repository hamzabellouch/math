import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.IncidenceDegree
import OAI.Probability.CriticalPercolation.Exploration.IncidenceIdentity
import OAI.Probability.CriticalPercolation.Exploration.QueryBand
import OAI.Probability.CriticalPercolation.Exploration.QueryNormalized
import OAI.Probability.CriticalPercolation.Modular.CappedDiscrepancy

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma clusterDiscrepancy_eq_centered (p : ℝ) (hp : p≠0) (ω : Set E) (v : V) :
    G.clusterDiscrepancy p ω v = -(IncidenceSearch.tree G v).centeredSum p ω / p := by
  rw [IncidenceSearch.tree_centered,clusterDiscrepancy,← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  change (if e∈G.incidentEdges (G.cluster ω v) then
      (if e∈ω then -(1-p)/p else 1) else 0) =
    -(if e∈G.incidentEdges (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0)/p
  by_cases he : e∈G.incidentEdges (G.cluster ω v)
  · by_cases hω : e∈ω <;> simp [he,hω,hp]
  · simp [he]

lemma root_discrepancy_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p ∅) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D) (K : ℕ) (v : V) :
    expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) ≤
      (D:ℝ)/p*(6/(2:ℝ)^K) := by
  let t := IncidenceSearch.tree G v
  have hwel : ∀ ω : Set E, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v| ≤
      (D:ℝ)/p * (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := by
    intro ω
    rw [G.clusterDiscrepancy_eq_centered p hp.1.ne' ω v,abs_div,abs_neg,abs_of_pos hp.1]
    change G.rootMass (cappedMass (4^K)) ω v * (|t.centeredSum p ω|/p) ≤ _
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p]
      simp
    · have hTD : t.queryCount ω ≤ D*G.clusterSize ω v := by
        rw [IncidenceSearch.tree_count]
        simpa only [clusterSize,mul_comm] using G.incident_card_le (G.cluster ω v) D hD
      have hh := G.capped_root_le_normalized (4^K) (t.queryCount ω) D
        (by positivity) (Nat.pos_of_ne_zero hT) hDpos ω v hTD
      have hh' : G.rootMass (cappedMass (4^K)) ω v ≤ (D:ℝ)*
          min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      calc
        _ ≤ ((D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) *
            (|t.centeredSum p ω|/p) := mul_le_mul_of_nonneg_right hh'
              (div_nonneg (abs_nonneg _) hp.1.le)
        _ = _ := by ring
  calc
    _ ≤ expect w (fun ω => (D:ℝ)/p *
        (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)))) := by
      exact expect_mono hn (fun ω => hwel ω)
    _ = (D:ℝ)/p * expect w (fun ω =>
        |t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := expect_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (t.normalized_centered_bound ∅ (IncidenceSearch.tree_valid G v) p
        ⟨hp.1.le,hp.2.le⟩ w hw hn hf K) (div_nonneg (Nat.cast_nonneg D) hp.1.le)

theorem finite_averaged_adjacent (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, prob w (BinaryLaw.endpointEvent G (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/p*(6/(2:ℝ)^K)) := by
  have hf : LazyDFS.Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  calc
    _ ≤ ∑ e, expect w (fun ω => G.edgeDiscrepancy (cappedMass (4^K)) p ω e) := by
      apply Finset.sum_le_sum
      intro e _
      exact G.endpoint_prob_le_discrepancy p hp w hw hn e (x e) (y e) (he e)
        (h0 e) (h1 e) (4^K) (by positivity)
    _ = expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * G.clusterDiscrepancy p ω v) := by
      erw [← expect_sum]
      congr 1
      funext ω
      exact G.sum_edgeDiscrepancy _ p ω
    _ ≤ expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      apply expect_mono hn
      intro ω
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left (le_abs_self _)
      exact div_nonneg (cappedMass_nonneg _ _) (Nat.cast_nonneg _)
    _ = ∑ v, expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      erw [expect_sum]
    _ ≤ ∑ _v : V, (D:ℝ)/p*(6/(2:ℝ)^K) := by
      exact Finset.sum_le_sum (fun v _ => G.root_discrepancy_bound p hp w hw hn hf D hDpos hD K v)
    _ = _ := by simp

end BondGraph
end CriticalPercolation
end
end
end

end OAI
