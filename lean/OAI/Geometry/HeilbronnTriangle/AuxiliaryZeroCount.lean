import OAI.Geometry.HeilbronnTriangle.ZeroGlobalCount
import OAI.Geometry.HeilbronnTriangle.AuxiliaryZeroWeights

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryZeroCount

open Matrix PrimitiveNormal ZeroDeterminantCount LiftingProbability
open scoped BigOperators

def countConstant : ℝ :=
  ZeroGlobalCount.countConstant 8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)

lemma countConstant_nonneg : 0 ≤ countConstant :=
  ZeroGlobalCount.countConstant_nonneg (by norm_num) (by positivity) (by positivity)

theorem weighted_count_le_log
    (D : RowData) (q N : ℕ) [Fact q.Prime]
    (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
    (hparam : D.h ^ 26 ≤ (q : ℝ))
    (L : AuxiliarySampling.Law q ((D.B ^ D.k) ^ 2))
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hdet : ∀ A ∈ S, A.det = 0)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
    (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ)) :
    (∑ A ∈ S, auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2 *
        (Real.log (4 * (N : ℝ)) / Real.log 2) := by
  apply ZeroGlobalCount.weighted_count_le_log D q N hN hEq hparam S
    (fun A => auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)
    (by norm_num) (by positivity) (by positivity)
    (fun A _ => auxiliaryWeight_nonneg q L.size L.weight L.sets L.weight_nonneg _)
    hdet hrows hheight hproj hbound
  · intro A hA hpositive
    obtain ⟨ω, hω⟩ := L.exists_outcome_of_weight_pos
      (A.map (Int.castRingHom (ZMod q))).col hpositive
    exact ⟨L.sets ω, L.isCap ω, hω⟩
  · intro A hA hAI
    exact L.weight_le_eight _ hAI
  · intro A hA
    simpa only [RowData.h, Nat.cast_pow] using
      L.weight_le_two_main_square (A.map (Int.castRingHom (ZMod q))).col
  · intro A hA hne
    simpa only [RowData.h, Nat.cast_pow] using
      L.weight_le_four_main_square (A.map (Int.castRingHom (ZMod q))).col hne
  · intro A hA x hx hkernel hAI hpositive
    simpa only [RowData.h, Nat.cast_pow] using
      L.kernel_norm_gt_main_square A hpositive hAI hx.ne_zero hkernel

end Problem355.AuxiliaryZeroCount

end

end OAI
