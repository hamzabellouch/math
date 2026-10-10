import OAI.GroupTheory.PolycyclicRecognition.Analysis.InvariantMeanGenerators
import OAI.GroupTheory.Thompson.FiniteAverage
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Invariant means on cyclic groups from literal power averages -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology BigOperators ENNReal

variable {G : Type*} [Group G]

def cyclicMeanState (a : G) (n : ℕ) : BoundedReal G →ₗ[ℝ] ℝ where
  toFun f := realAvg (Finset.range (n + 1)) (fun k => f (a ^ k))
  map_add' _f _g := realAvg_add _ _ _
  map_smul' r _f := realAvg_const_mul _ r _

theorem cyclicMeanState_positive (a : G) (n : ℕ) (f : BoundedReal G)
    (hf : ∀ g, 0 ≤ f g) : 0 ≤ cyclicMeanState a n f :=
  realAvg_nonneg _ (fun k _ => hf (a ^ k))

theorem cyclicMeanState_one (a : G) (n : ℕ) : cyclicMeanState a n 1 = 1 :=
  realAvg_const _ (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) 1

/-- The generator defect telescopes without any injectivity assumption on
the powers. The same averages work for finite and infinite cyclic groups. -/
theorem cyclicMeanState_generator_defect (a : G) (n : ℕ) (f : BoundedReal G) :
    cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f =
      (f (a ^ (n + 1)) - f 1) / ((n : ℝ) + 1) := by
  have havg (v : ℕ → ℝ) :
      realAvg (Finset.range (n + 1)) (fun k => v (k + 1) - v k) =
        (v (n + 1) - v 0) / ((n : ℝ) + 1) := by
    rw [realAvg, Finset.sum_range_sub]
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
  have hpull : (fun k : ℕ => leftPull a f (a ^ k)) =
      (fun k : ℕ => f (a ^ (k + 1))) := by
    funext k
    rw [leftPull_apply, pow_succ']
  change realAvg (Finset.range (n + 1)) (fun k => leftPull a f (a ^ k)) -
    realAvg (Finset.range (n + 1)) (fun k => f (a ^ k)) = _
  rw [hpull, ← realAvg_sub]
  simpa only [pow_zero] using havg (fun k => f (a ^ k))

theorem invariantMean_of_zpowers_eq_top (a : G) (ha : Subgroup.zpowers a = ⊤) :
    Nonempty (InvariantMean G) := by
  apply exists_invariantMean_of_approximate_generators (l := atTop)
    (cyclicMeanState a) (cyclicMeanState_positive a) (cyclicMeanState_one a) {a}
    (by rwa [← Subgroup.zpowers_eq_closure])
  intro g hg f
  have hga : g = a := mem_singleton_iff.mp hg
  subst g
  have hbound (n : ℕ) :
      ‖cyclicMeanState a n (leftPull a f) - cyclicMeanState a n f‖ ≤
        (2 * ‖f‖) / ((n : ℝ) + 1) := by
    rw [Real.norm_eq_abs, cyclicMeanState_generator_defect, abs_div,
      abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h₁ := lp.norm_apply_le_norm ENNReal.top_ne_zero f (a ^ (n + 1))
    have h₂ := lp.norm_apply_le_norm ENNReal.top_ne_zero f 1
    have hsub := abs_sub (f (a ^ (n + 1))) (f 1)
    simp only [Real.norm_eq_abs] at h₁ h₂
    linarith
  apply squeeze_zero_norm hbound
  simpa only [div_eq_mul_inv, one_mul, mul_zero, mul_assoc] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)

theorem invariantMean_of_isCyclic [IsCyclic G] : Nonempty (InvariantMean G) := by
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  exact invariantMean_of_zpowers_eq_top a ha

end PolycyclicRecognition

end

end OAI
