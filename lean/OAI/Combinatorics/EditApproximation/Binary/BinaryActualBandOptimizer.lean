import OAI.Combinatorics.EditApproximation.Binary.BinaryBandEnvelope
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOptimizer

namespace OAI

/-! The complete Boolean band optimizer constructs its envelopes from the
stored initial table, then constructs the vertices and history vector. The
normalized history bounds follow from actual band-coordinate membership. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem listedBandCoordinateVector_coverage {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (i : Fin (listedBandCoordinates band).length) :
    ∃ action ∈ band, action ((listedBandCoordinateVector band).get i).1 =
      ((listedBandCoordinateVector band).get i).2 := by
  have hc : (listedBandCoordinateVector band).get i ∈ listedBandCoordinates band := by
    simp only [listedBandCoordinateVector, vector_get_ofFn]
    exact List.get_mem _ _
  obtain ⟨action, ha, hc⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hc)
  obtain ⟨child, hchild⟩ := List.mem_ofFn.mp hc
  refine ⟨action, ha, ?_⟩
  rw [← hchild]

def envelopeVectorWithWork {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) : Vector BinaryFraction M × ℕ :=
  vectorMapWithWork M (bandEnvelopeWithWork b band initial)

theorem envelopeVectorWithWork_value {M ny : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → BinaryFraction) (hb : 0 < b) (i : Fin M) :
    ((envelopeVectorWithWork b band initial).1.get i).value =
      bandChildEnvelope b band (fun j q => (initial j q).value) i := by
  simp only [envelopeVectorWithWork, vectorMapWithWork_value]
  exact bandEnvelopeWithWork_value b band initial i hb

def bandOptimizerWithWork {M d ny : ℕ}
    (coordinates : Vector (Fin M × TargetInterval ny) d) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (G K t : ℕ) : Vector BinaryFraction d × ℕ :=
  let mass := envelopeVectorWithWork b band initial
  let result := preparedBandOptimizerWithWork coordinates mass.1 table eta kappa band G K t
  (result.1, mass.2 + result.2 + 1)

theorem bandOptimizerWithWork_value {M d ny : ℕ}
    (coordinates : Vector (Fin M × TargetInterval ny) d) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (G K t : ℕ) (hb : 0 < b) :
    (fun i => ((bandOptimizerWithWork coordinates b initial table eta kappa band G K t).1.get i).value) =
      finiteRationalOptimizer univ
        (band.map fun action i => actionVector
          (bandChildEnvelope b band (fun j q => (initial j q).value)) action (coordinates.get i))
        (fun i => rationalOnlineLinear eta.value kappa.value
          (childGain (bandChildEnvelope b band (fun j q => (initial j q).value))
            (fun s j => (table s j).value))
          (childDecrement (bandChildEnvelope b band (fun j q => (initial j q).value))
            (fun s j => (table s j).value)) t (coordinates.get i)) G K := by
  simp only [bandOptimizerWithWork, preparedBandOptimizerWithWork_value]
  have hm : (fun j => ((envelopeVectorWithWork b band initial).1.get j).value) =
      bandChildEnvelope b band (fun j q => (initial j q).value) := by
    funext j
    exact envelopeVectorWithWork_value b band initial hb j
  rw [hm]

def actualBandOptimizerBitBudget (M d b vertices G K t Be Bk Bi Bt E : ℕ) : ℕ :=
  M * (bandEnvelopeBitBudget b M vertices Bi + 6) +
    preparedBandOptimizerBitBudget M d vertices G K t Be Bk
      (3 * bandEnvelopeWordBudget b M Bi + 1) Bt E + 1

theorem bandOptimizerWithWork_cost {M d ny : ℕ}
    (coordinates : Vector (Fin M × TargetInterval ny) d) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (G K t Be Bk Bi Bt E : ℕ)
    (hband : band ≠ []) (hb : 0 < b) (hM : 0 < M)
    (hcoverage : ∀ i, ∃ action ∈ band, action (coordinates.get i).1 = (coordinates.get i).2)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s (coordinates.get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i, 0 ≤ (table s (coordinates.get i)).value ∧
      (table s (coordinates.get i)).value ≤ (initial (coordinates.get i).1 (coordinates.get i).2).value) :
    (bandOptimizerWithWork coordinates b initial table eta kappa band G K t).2 ≤
      actualBandOptimizerBitBudget M d b band.length G K t Be Bk Bi Bt E := by
  let mass := (envelopeVectorWithWork b band initial).1
  have hmv (j : Fin M) : (mass.get j).value = bandChildEnvelope b band (fun j q => (initial j q).value) j :=
    envelopeVectorWithWork_value b band initial hb j
  have hm (j : Fin M) : (mass.get j).width ≤ 3 * bandEnvelopeWordBudget b M Bi + 1 := by
    simp only [mass, envelopeVectorWithWork, vectorMapWithWork_value]
    exact bandEnvelopeWithWork_width b band initial j Bi (fun action ha => hi action ha j)
  have hmpos (j : Fin M) : 0 < (mass.get j).value := by
    rw [hmv]
    exact lt_of_lt_of_le (div_pos (by exact_mod_cast hb) (by exact_mod_cast hM))
      (bandChildEnvelope_lower b band (fun j q => (initial j q).value) j).1
  have hnormalized (s : ℕ) (hs : s ≤ t + 1) (i : Fin d) :
      0 ≤ (table s (coordinates.get i)).value ∧
        (table s (coordinates.get i)).value ≤ (mass.get (coordinates.get i).1).value := by
    refine ⟨(htrange s hs i).1, ?_⟩
    obtain ⟨action, ha, heq⟩ := hcoverage i
    have henv := (bandChildEnvelope_lower b band (fun j q => (initial j q).value)
      (coordinates.get i).1).2 action ha
    rw [heq] at henv
    rw [hmv]
    exact (htrange s hs i).2.trans henv
  have hp := preparedBandOptimizerWithWork_cost coordinates mass table eta kappa band G K t
    Be Bk (3 * bandEnvelopeWordBudget b M Bi + 1) Bt E hband he hk hm hmpos ht heabs hkrange hnormalized
  have hc := vectorMapWithWork_cost_le M (bandEnvelopeWithWork b band initial)
    (bandEnvelopeBitBudget b M band.length Bi)
    (fun j => bandEnvelopeWithWork_cost b band initial j Bi (fun action ha => hi action ha j))
  change (envelopeVectorWithWork b band initial).2 +
    (preparedBandOptimizerWithWork coordinates mass table eta kappa band G K t).2 + 1 ≤ _
  change (envelopeVectorWithWork b band initial).2 ≤ _ at hc
  unfold actualBandOptimizerBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
