import OAI.Geometry.HeilbronnTriangle.NonzeroWeightedCount
import OAI.Geometry.HeilbronnTriangle.SmallDeterminantWeight
import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingLaw

namespace OAI


noncomputable section
namespace Problem355.NonzeroAuxiliaryCount

open NonzeroWeightedCount
open scoped BigOperators

def countConstant : ℝ := 8 * boxConstant

lemma countConstant_pos : 0 < countConstant := mul_pos (by norm_num) boxConstant_pos

theorem weighted_orbit_count
    {B k q : ℕ} (hB : 0 < B) [Fact q.Prime]
    [Fintype ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (U : Finset (Fin 3 → ZMod q)) (hU : U.Nonempty)
    (T : Finset ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)))
    (hT : T.Nonempty)
    (hsize : Fintype.card ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)) ≤
      2 * T.card)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (t : ℤ) (ht : t ≠ 0) (htq : |t| < (q : ℤ)) (hdet : ∀ A ∈ S, A.det = t) :
    (∑ A ∈ S, AuxiliaryWeights.affineInclusionWeight U T
      (fun j i => (A i j : ZMod q))) ≤
        countConstant * Real.log (2 * N) ^ 2 * N ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  apply NonzeroWeightedCount.weighted_orbit_count B k d.b d.e hB d.b_le_k d.e_le_k
    d.b_le_e C d.left d.right _ N hN S horbit hbox t ht hdet _ 8 (by norm_num)
  · intro A hA
    exact SmallDeterminantWeight.weight_le_eight U hU T hT hsize A
      (by simpa only [hdet A hA] using ht) (by simpa only [hdet A hA] using htq)
  · simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem weighted_law_count
    {B k q H : ℕ} (hB : 0 < B) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (aux : AuxiliarySampling.Law q H)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (t : ℤ) (ht : t ≠ 0) (htq : |t| < (q : ℤ)) (hdet : ∀ A ∈ S, A.det = t) :
    (∑ A ∈ S, LiftingProbability.auxiliaryWeight q aux.size aux.weight aux.sets
      (fun j i => (A i j : ZMod q))) ≤
        countConstant * Real.log (2 * N) ^ 2 * N ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  apply NonzeroWeightedCount.weighted_orbit_count B k d.b d.e hB d.b_le_k d.e_le_k
    d.b_le_e C d.left d.right _ N hN S horbit hbox t ht hdet _ 8 (by norm_num)
  · intro A hA
    apply aux.weight_le_eight
    exact SmallDeterminantWeight.affineIndependent_columns A
      (by simpa only [hdet A hA] using ht) (by simpa only [hdet A hA] using htq)
  · simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

end Problem355.NonzeroAuxiliaryCount

end

end OAI
