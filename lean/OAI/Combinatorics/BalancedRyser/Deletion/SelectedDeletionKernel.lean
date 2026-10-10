import Mathlib
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletion

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Balanced.SelectedDeletion

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

structure FixedLaw (M : MergedPairs F) (K ρ ε : ℝ) where
  weight : Output F → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  mass_le_one : (∑ s, weight s) ≤ 1
  supported : ∀ s, 0 < weight s →
    (configuration M s).Valid ∧ (configuration M s).Compatible
  success_lower : 1 - ε ≤ ∑ s, weight s
  cylinder_le : ∀ (J : Finset (Slot F)) (prescribed : Output F),
    (∑ s, if ∀ i ∈ J, s i = prescribed i then weight s else 0) ≤
      (K / (Fintype.card F : ℝ)) ^ J.card
  occupancy_le :
    (∑ s, if ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊
      then weight s else 0) ≤ ε

theorem occupancy_mono {M : MergedPairs F} {s : Output F} {ρ ρ' : ℝ} {B : ℕ}
    (hρ : ρ' ≤ ρ) (h : (configuration M s).Occupancy ρ B) :
    (configuration M s).Occupancy ρ' B := by
  refine ⟨h.1, ?_, ?_⟩
  · intro l hl
    exact (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)).trans (h.2.1 l hl)
  · intro d
    exact (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)).trans (h.2.2 d)

def FixedLaw.relax {M : MergedPairs F} {K K' ρ ρ' ε : ℝ}
    (law : FixedLaw M K ρ ε) (hK : 0 ≤ K) (hKK : K ≤ K') (hρ : ρ' ≤ ρ) :
    FixedLaw M K' ρ' ε where
  weight := law.weight
  nonnegative := law.nonnegative
  mass_le_one := law.mass_le_one
  supported := law.supported
  success_lower := law.success_lower
  cylinder_le := by
    intro J prescribed
    exact (law.cylinder_le J prescribed).trans
      (pow_le_pow_left₀ (div_nonneg hK (Nat.cast_nonneg _))
        (div_le_div_of_nonneg_right hKK (Nat.cast_nonneg _)) J.card)
  occupancy_le := by
    apply le_trans _ law.occupancy_le
    apply sum_le_sum
    intro s _
    by_cases hs : ¬ (configuration M s).Occupancy ρ' ⌈Real.log (Fintype.card F : ℝ)⌉₊
    · have ht : ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ :=
        fun h => hs (occupancy_mono hρ h)
      simp [hs, ht]
    · simp only [hs, ite_false]
      split_ifs
      · exact le_rfl
      · exact law.nonnegative s

def glue {c C K ρ ε : ℝ}
    (laws : ∀ M : MergedPairs F, InitialGood M c C → FixedLaw M K ρ ε) : Kernel F :=
  fun M s => if h : InitialGood M c C then (laws M h).weight s else 0

variable {c C K ρ ε : ℝ}
variable (laws : ∀ M : MergedPairs F, InitialGood M c C → FixedLaw M K ρ ε)

theorem glue_isExperiment : IsExperiment (glue laws) c C := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M s
    by_cases h : InitialGood M c C
    · simpa [glue, h] using (laws M h).nonnegative s
    · simp [glue, h]
  · intro M
    by_cases h : InitialGood M c C
    · simpa [glue, h] using (laws M h).mass_le_one
    · simp [glue, h]
  · intro M h s
    simp [glue, h]
  · intro M s hs
    by_cases h : InitialGood M c C
    · exact (laws M h).supported s (by simpa [glue, h] using hs)
    · simp [glue, h] at hs

theorem glue_fixedSuccessMass (M : MergedPairs F) (h : InitialGood M c C) :
    1 - ε ≤ fixedSuccessMass (glue laws) M := by
  simpa [fixedSuccessMass, glue, h] using (laws M h).success_lower

theorem glue_fixedCylinderMass_le (hK : 0 ≤ K) (M : MergedPairs F)
    (J : Finset (Slot F)) (prescribed : Output F) :
    fixedCylinderMass (glue laws) M J prescribed ≤
      (K / (Fintype.card F : ℝ)) ^ J.card := by
  classical
  by_cases h : InitialGood M c C
  · simpa [fixedCylinderMass, glue, h] using (laws M h).cylinder_le J prescribed
  · simp only [fixedCylinderMass, glue, h, dite_false, ite_self, sum_const_zero]
    positivity

theorem offset_sum_real : ∑ M : MergedPairs F, ((offsetLaw F) M).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun M _ => (offsetLaw F).apply_ne_top M)]
  have h : ∑ M : MergedPairs F, (offsetLaw F) M = 1 := by
    simpa only [tsum_fintype] using (offsetLaw F).tsum_coe
  rw [h]
  simp

theorem offsetEventProbability_eq_sum (P : MergedPairs F → Prop) :
    offsetEventProbability {M | P M} =
      ∑ M, if P M then ((offsetLaw F) M).toReal else 0 := by
  classical
  unfold offsetEventProbability
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro M _
    by_cases h : P M <;> simp [Set.indicator, h]
  · intro M _
    by_cases h : P M <;> simp [Set.indicator, h, (offsetLaw F).apply_ne_top]

theorem glue_occupancyFailureMass_le (hε : 0 ≤ ε) :
    occupancyFailureMass (glue laws) ρ ≤ ε := by
  classical
  unfold occupancyFailureMass jointMass
  calc
    _ ≤ ∑ M : MergedPairs F, ((offsetLaw F) M).toReal * ε := by
      apply sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases h : InitialGood M c C
      · refine le_trans (le_of_eq ?_) (laws M h).occupancy_le
        apply sum_congr rfl
        intro output _
        by_cases hocc : (configuration M output).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ <;>
          simp [glue, h, hocc]
      · simpa [glue, h] using hε
    _ = ε := by rw [← sum_mul, offset_sum_real, one_mul]

theorem glue_successMass_lower :
    (1 - ε) * offsetEventProbability {M : MergedPairs F | InitialGood M c C} ≤
      successMass (glue laws) := by
  classical
  rw [offsetEventProbability_eq_sum]
  unfold successMass jointMass
  rw [mul_sum]
  apply sum_le_sum
  intro M _
  by_cases h : InitialGood M c C
  · simp only [h, ite_true]
    rw [mul_comm (1 - ε)]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [glue, h] using (laws M h).success_lower
  · simp [glue, h]

theorem glue_successMass_lower_half {p : ℝ} (hp : 0 ≤ p)
    (hgood : p ≤ offsetEventProbability {M : MergedPairs F | InitialGood M c C})
    (hε : ε ≤ 1 / 2) : p / 2 ≤ successMass (glue laws) := by
  have hP : 0 ≤ offsetEventProbability {M : MergedPairs F | InitialGood M c C} :=
    hp.trans hgood
  have hprod : 0 ≤ (1 / 2 - ε) *
      offsetEventProbability {M : MergedPairs F | InitialGood M c C} :=
    mul_nonneg (sub_nonneg.mpr hε) hP
  exact (by nlinarith : p / 2 ≤ (1 - ε) *
    offsetEventProbability {M : MergedPairs F | InitialGood M c C}).trans
    (glue_successMass_lower laws)

theorem exists_kernel_of_fixedLaws (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (available : ∀ M : MergedPairs F, InitialGood M c C →
      Nonempty (FixedLaw M K ρ ε)) :
    ∃ κ : Kernel F, IsExperiment κ c C ∧
      (∀ M, InitialGood M c C → 1 - ε ≤ fixedSuccessMass κ M) ∧
      (∀ M (J : Finset (Slot F)) (prescribed : Output F),
        fixedCylinderMass κ M J prescribed ≤ (K / (Fintype.card F : ℝ)) ^ J.card) ∧
      occupancyFailureMass κ ρ ≤ ε ∧
      (1 - ε) * offsetEventProbability {M : MergedPairs F | InitialGood M c C} ≤
        successMass κ := by
  let chosen : ∀ M : MergedPairs F, InitialGood M c C → FixedLaw M K ρ ε :=
    fun M h => Classical.choice (available M h)
  exact ⟨glue chosen, glue_isExperiment chosen, glue_fixedSuccessMass chosen,
    glue_fixedCylinderMass_le chosen hK, glue_occupancyFailureMass_le chosen hε,
    glue_successMass_lower chosen⟩

end Balanced.SelectedDeletion

end

end OAI
