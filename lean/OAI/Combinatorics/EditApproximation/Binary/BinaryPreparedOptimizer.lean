import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineInputWork

namespace OAI

/-! The complete Boolean optimizer call, including construction of its
vertices and optimistic linear vector from stored input fractions. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def preparedBandOptimizerWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ) : Vector BinaryFraction d × ℕ :=
  let vertices := bandVerticesWithWork coordinates mass band
  let linear := vectorMapWithWork d fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)
  let answer := finiteOptimizerWithWork vertices.1 linear.1 G K
  (answer.1, vertices.2 + linear.2 + answer.2 + 2)

theorem preparedBandOptimizerWithWork_value {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ) :
    (fun i => ((preparedBandOptimizerWithWork coordinates mass table eta kappa band G K t).1.get i).value) =
      finiteRationalOptimizer univ
        (band.map fun action i => actionVector (fun j => (mass.get j).value) action (coordinates.get i))
        (fun i => rationalOnlineLinear eta.value kappa.value
          (childGain (fun j => (mass.get j).value) (fun s j => (table s j).value))
          (childDecrement (fun j => (mass.get j).value) (fun s j => (table s j).value))
          t (coordinates.get i)) G K := by
  simp only [preparedBandOptimizerWithWork, finiteOptimizerWithWork_value,
    bandVerticesWithWork_values, vectorMapWithWork_value, onlineLinearWithWork_value]

def preparedBandOptimizerBitBudget (M d vertices G K t Be Bk Bm Bt E : ℕ) : ℕ :=
  bandPreparationBitBudget M d vertices Bm +
    d * (onlineLinearBitBudget Be Bk Bm Bt t + 6) +
    optimizerBitBudget d vertices G K (bandVertexWordBudget M Bm) (bandVertexWordBudget M Bm)
      (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1)) + 2

theorem preparedBandOptimizerWithWork_cost {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (table : ℕ → Fin M × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t Be Bk Bm Bt E : ℕ)
    (hband : band ≠ []) (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hm : ∀ j, (mass.get j).width ≤ Bm) (hmpos : ∀ j, 0 < (mass.get j).value)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s (coordinates.get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i,
      0 ≤ (table s (coordinates.get i)).value ∧
        (table s (coordinates.get i)).value ≤ (mass.get (coordinates.get i).1).value) :
    (preparedBandOptimizerWithWork coordinates mass table eta kappa band G K t).2 ≤
      preparedBandOptimizerBitBudget M d band.length G K t Be Bk Bm Bt E := by
  let vertices := (bandVerticesWithWork coordinates mass band).1
  let linear := (vectorMapWithWork d fun i =>
    onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i)).1
  have hlength : vertices.length = band.length := by simp [vertices, bandVerticesWithWork]
  have hvertices : vertices ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlength
    exact hband (List.length_eq_zero_iff.mp hlength.symm)
  have hv (v : Vector BinaryFraction d) (hv : v ∈ vertices) (i : Fin d) :=
    bandVerticesWithWork_input_bounds coordinates mass band Bm hm hmpos v hv i
  have hlwidth (i : Fin d) : (linear.get i).width ≤ onlineLinearStorageBudget Be Bk Bm Bt t := by
    simp only [linear, vectorMapWithWork_value]
    exact onlineLinearWithWork_storage (fun j => mass.get j) table eta kappa t
      (coordinates.get i) Be Bk Bm Bt he hk (hm _) (fun s hs => ht s hs i)
  have hlvalue (i : Fin d) : |(linear.get i).value| ≤ (E * (2 * t + 1) : ℕ) := by
    simp only [linear, vectorMapWithWork_value, onlineLinearWithWork_value]
    have h := rationalOnlineLinear_abs (fun j => (mass.get j).value)
      (fun s j => (table s j).value) eta.value kappa.value t E (coordinates.get i)
      heabs (hmpos _) hkrange (fun s hs => htrange s hs i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h
  have hc := finiteOptimizerWithWork_cost vertices linear G K (bandVertexWordBudget M Bm)
    (bandVertexWordBudget M Bm) (onlineLinearStorageBudget Be Bk Bm Bt t) (E * (2 * t + 1))
    hvertices (fun v hv' i => ⟨(hv v hv' i).1, (hv v hv' i).2.1, (hv v hv' i).2.2.1⟩)
    (fun v hv' i => (hv v hv' i).2.2.2) hlwidth hlvalue
  rw [hlength] at hc
  have hp := bandVerticesWithWork_cost coordinates mass band Bm hm
  have hl := vectorMapWithWork_cost_le d
    (fun i => onlineLinearWithWork (fun j => mass.get j) table eta kappa t (coordinates.get i))
    (onlineLinearBitBudget Be Bk Bm Bt t) (fun i => onlineLinearWithWork_cost
      (fun j => mass.get j) table eta kappa t (coordinates.get i) Be Bk Bm Bt
      he hk (hm _) (fun s hs => ht s hs i))
  change (bandVerticesWithWork coordinates mass band).2 +
    (vectorMapWithWork d (fun i => onlineLinearWithWork (fun j => mass.get j)
      table eta kappa t (coordinates.get i))).2 +
    (finiteOptimizerWithWork vertices linear G K).2 + 2 ≤ _
  unfold preparedBandOptimizerBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
