import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.WitnessEmbeddingBound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma indexedWitnessCode_card_bound {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (mark : Fin K → Option (Fin s)) :
    Fintype.card (IndexedWitnessCode E birth mark) ≤ K^2*6^s := by
  simpa only [Fintype.card_fin] using all_marked_indexed_attachment_pattern_count E birth hE mark

lemma boundedEmbeddedWitness_weight_sum {n R d : ℕ} (G : Graph n) (r : ℕ)
    (hR : R ≤ 4) (hm : 0 ≤ prefixM n) (v : WitnessDimensions R d → ℝ)
    (hv : ∀ q, 0 ≤ v q) :
    (∑ W : BoundedEmbeddedWitness G R d, if WitnessEmbeddingBound r W then v W.1 else 0) ≤
      ∑ q : WitnessDimensions R d,
        64*(q.val.1.val^2*6^q.val.2.val : ℕ) *
          ((4*prefixM n)^r*(2*prefixD n)^q.val.2.val/prefixD n^50)*v q := by
  classical
  have hD : 0 ≤ prefixD n := by unfold prefixD; positivity
  let B (q : WitnessDimensions R d) :=
    (4*prefixM n)^r*(2*prefixD n)^q.val.2.val/prefixD n^50
  have hB (q : WitnessDimensions R d) : 0 ≤ B q := by dsimp only [B]; positivity
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  rw [Fintype.sum_sigma]
  have hqR : R ≤ q.val.1.val := by have h := q.property; omega
  calc
    _ ≤ ∑ E : {E : Graph q.val.1 // E ∈ seedPatternChoices q.val.1 R},
        (q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q := by
      apply Finset.sum_le_sum
      intro E _
      let Code := IndexedWitnessCode E.val (dimensionBirth q) (suffixProjection q.property)
      have hc := indexedWitnessCode_card_bound E.val (dimensionBirth q)
        (Finset.mem_filter.mp E.property).2 (suffixProjection q.property)
      rw [Fintype.sum_sigma]
      calc
        _ ≤ ∑ _w : Code, B q*v q := by
          apply Finset.sum_le_sum
          intro w _
          change (∑ _ψ : {ψ : Fin q.val.1 ↪ Fin n //
            ψ ∈ graphEmbeddingSet (decodeWitnessPattern w).2 G},
            if ((graphEmbeddingSet (decodeWitnessPattern w).2 G).card : ℝ) ≤ B q
              then v q else 0) ≤ B q*v q
          by_cases hh : ((graphEmbeddingSet (decodeWitnessPattern w).2 G).card : ℝ) ≤ B q
          · simp only [hh,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hh (hv q)
          · simp only [hh,ite_false,Finset.sum_const_zero]
            exact mul_nonneg (hB q) (hv q)
        _ = (Fintype.card Code : ℝ)*B q*v q := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hB q)) (hv q)
    _ = (seedPatternChoices q.val.1 R).card *
        ((q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ ≤ 64*((q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q) := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (seedPatternChoices_card hqR hR))
        (mul_nonneg (mul_nonneg (by positivity) (hB q)) (hv q))
    _ = _ := by dsimp only [B]; ring

end SharpTerminalLeave

open scoped BigOperators Topology
open Filter

end

end OAI
