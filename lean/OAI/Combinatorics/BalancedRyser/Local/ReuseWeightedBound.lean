import OAI.Combinatorics.BalancedRyser.Local.ReuseSchedule
import OAI.Combinatorics.BalancedRyser.Local.ReuseScheduleAggregation
import OAI.Combinatorics.BalancedRyser.Local.ReuseScore

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def extensionConstant : ℝ := 4 * (4096 * 24 ^ 4)

def reuseBoundConstant (K : ℝ) : ℝ :=
  19531 * (max 1 (extensionConstant * K)) ^ 6

theorem reuseBoundConstant_pos (K : ℝ) : 0 < reuseBoundConstant K :=
  ReuseSchedule.aggregate_constant_pos (extensionConstant * K)

def weightedWitnessMass (K : ℝ) (p : Point F) (n : ℕ) : ℝ :=
  ∑ a : Fin n → Prescription F,
    if 3 ≤ reuseExposureScore prescriptionGenerators (List.ofFn a).reverse then
      prefixWeight K p (List.ofFn a).reverse else 0

theorem sum_weightedWitnessMass_le_of_prefix_extensions (K : ℝ) (hK : 0 ≤ K)
    (p : Point F)
    (hstep : ∀ pre : List (Prescription F), pre.length < 6 →
      ∀ j : ℕ, j ≤ 4 →
      (∑ r : Prescription F, if oldCount pre r = j then
        prefixWeight K p (r :: pre) else 0) ≤
        (extensionConstant * K / (Fintype.card F : ℝ) ^ reuseSaving j) *
          prefixWeight K p pre) :
    (∑ n : Fin 7, weightedWitnessMass K p n.val) ≤
      reuseBoundConstant K / (Fintype.card F : ℝ) ^ 3 := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hC : 0 ≤ extensionConstant * K := by
    unfold extensionConstant
    positivity
  apply ReuseSchedule.sum_length_masses_le (extensionConstant * K)
    (Fintype.card F) hC hq (fun n => weightedWitnessMass K p n.val)
  intro n
  have h := ReuseSchedule.sum_reuse_witness_weights_le
    prescriptionGenerators prescriptionGenerators_card_le_four
    (prefixWeight K p) 6 n.val 3 (Fintype.card F) (extensionConstant * K) hq hC
    (prefixWeight_nonneg K hK p) ?_ (by omega)
  · simpa only [weightedWitnessMass, prefixWeight_nil, mul_one] using h
  intro pre hp j hj
  simp_rw [category_cutoff_weight_eq]
  exact hstep pre hp j hj

end
end Balanced.ReuseTower

end OAI
