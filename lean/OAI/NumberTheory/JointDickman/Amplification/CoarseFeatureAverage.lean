import OAI.NumberTheory.JointDickman.Amplification.CoarseCellUnion
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCoarseFeatures
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMarginal
import OAI.NumberTheory.JointDickman.Amplification.FairAverageContraction

namespace OAI

/-! # Coarse features are conditional averages of fixed logarithmic intervals -/
namespace JointDickman
open Finset Classical

noncomputable def coarseLogTest {m : ℕ} (d : Fin m) (s : ℝ) : ℝ :=
  if s ∈ Set.Ioc (channelLower m d) (channelUpper m d) then 1/channelMesh m else 0

theorem primeCoarseFeature_eq_average {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (d : Fin m) (x : auxiliaryPrimes B → Bool) :
    primeCoarseFeature m B d x = fairSplitAverage x (fun y =>
      coarseLogTest d (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B)) := by
  have hk := channelBlockCount_pos hm hB
  unfold primeCoarseFeature primeGroupedTransition partialFairPrimeTransition optionCellMass
  simp_rw [logarithmicCell_eq_some B _ _ (groupedCells_disjoint hm hk)]
  rw [sum_comm]
  unfold fairSplitAverage
  rw [sum_div]
  apply sum_congr rfl
  intro y _
  have he := groupedCell_indicator_sum hm hk d
    (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B)
  have hs : (∑ r : Fin (channelBlockCount m B),
      if Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B ∈
        Set.Ioc (groupedLower m (channelBlockCount m B) (d,r))
          (groupedUpper m (channelBlockCount m B) (d,r))
      then fairRetentionMass x y else 0) = fairRetentionMass x y*
      (∑ r : Fin (channelBlockCount m B),
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B ∈
          Set.Ioc (groupedLower m (channelBlockCount m B) (d,r))
            (groupedUpper m (channelBlockCount m B) (d,r)) then (1 : ℝ) else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp
  rw [hs,he]
  unfold coarseLogTest
  split_ifs <;> simp_all only [ite_true,ite_false,mul_one,mul_zero,zero_mul,div_eq_mul_inv,one_mul]

theorem primeCoarseFeature_average_error {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (d : Fin m) (q : ℝ → ℝ) :
    (∑ x, fullPrimeMass (auxiliaryPrimes B) x*
      (primeCoarseFeature m B d x-fairSplitAverage x (fun y =>
        q (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B)))^2) ≤
      ∑ y, bernoulliSiteMass (fun p : auxiliaryPrimes B => 1/(2*(p.val : ℝ))) y*
        (coarseLogTest d (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B)-
          q (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B))^2 := by
  simp_rw [primeCoarseFeature_eq_average hm hB]
  have hq : ∀ p : auxiliaryPrimes B, 0 ≤ 1/(p.val : ℝ) ∧ 1/(p.val : ℝ) ≤ 1 := by
    intro p
    have hp := (auxiliaryPrimes_prime B p.val p.property).two_le
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast (show 0 < p.val by omega))).mpr (by exact_mod_cast (show 1 ≤ p.val by omega))
  convert fairSplitAverage_square_error (fun p : auxiliaryPrimes B => 1/(p.val : ℝ)) hq
    (fun y => coarseLogTest d (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B))
    (fun y => q (Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B)) using 1
  · rfl
  · congr 1
    funext y
    congr 1
    unfold bernoulliSiteMass
    congr 1
    funext p
    congr 1
    ring

end JointDickman

end OAI
