import OAI.NumberTheory.PrimePackets.ObservationRefinement
import OAI.NumberTheory.PrimePackets.EntropyMixtures

namespace OAI

/-! # Positive entropy survives the fourth iterate

The regular weights used in the finite coefficient-balance test are four
times the original regular weights. Grouping four consecutive symbols
transfers positive metric entropy to that time-four map. Only this fixed
iterate is needed here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

private def fourWordEquiv (α : Type*) (N : ℕ) :
    (Fin N → Fin 4 → α) ≃ (Fin (N * 4) → α) where
  toFun w l := w (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  invFun w i j := w (finProdFinEquiv (i,j))
  left_inv w := by funext i j; simp
  right_inv w := by
    funext l
    change w (finProdFinEquiv (finProdFinEquiv.symm l)) = w l
    rw [Equiv.apply_symm_apply]

private lemma orbitName_four_blocks {Y α : Type*}
    (T : Y → Y) (P : Y → α) (N : ℕ) :
    orbitName T P (N * 4) = fun y =>
      fourWordEquiv α N (orbitName (T^[4]) (orbitName T P 4) N y) := by
  funext y
  apply (fourWordEquiv α N).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i j
  change P (T^[j.val + 4 * i.val] y) = P (T^[j.val] ((T^[4])^[i.val] y))
  rw [Function.iterate_add_apply, Function.iterate_mul]

private lemma observationEntropyRate_recode {Y α β : Type*}
    [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) (e : α ≃ β) :
    observationEntropyRate μ T (fun y => e (P y)) = observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  congr 1
  have hi : Function.Injective (fun w : Fin N → α => fun i => e (w i)) := by
    intro w v h
    funext i
    exact e.injective (congrFun h i)
  exact observationEntropy_injective μ (orbitName T P N) _ hi

/-- Four-symbol blocks have four times the original entropy rate. -/
theorem observationEntropyRate_four_blocks {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ (T^[4]) (orbitName T P 4) =
      4 * observationEntropyRate μ T P := by
  have hsub : Tendsto (fun N : ℕ => N * 4) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have H := (tendsto_observationEntropyRate μ hT P hP).comp hsub
  have hscaled : Tendsto (fun N : ℕ => 4 *
      (observationEntropy μ (orbitName T P (N * 4)) / (N * 4 : ℕ))) atTop
      (𝓝 (4 * observationEntropyRate μ T P)) := tendsto_const_nhds.mul H
  have heq : (fun N : ℕ => 4 *
      (observationEntropy μ (orbitName T P (N * 4)) / (N * 4 : ℕ))) =
      (fun N : ℕ =>
        observationEntropy μ (orbitName (T^[4]) (orbitName T P 4) N) / N) := by
    funext N
    rw [orbitName_four_blocks, observationEntropy_equiv]
    by_cases hN : N = 0
    · subst N
      simp
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    push_cast
    field_simp [hN']
  rw [heq] at hscaled
  exact tendsto_nhds_unique
    (tendsto_observationEntropyRate μ (hT.iterate 4) (orbitName T P 4)
      (orbitName_measurable_fiber hT.measurable hP 4)) hscaled

/-- Vanishing entropy of the time-four map forces vanishing entropy of
the original map. This uses the actual supremum over finite observations. -/
theorem measureEntropy_eq_zero_of_fourth_iterate {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hzero : measureEntropy μ (T^[4]) = 0) :
    measureEntropy μ T = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  let e := Fintype.equivFin (Fin 4 → Fin k)
  let Q := fun y => e (orbitName T P 4 y)
  have hQ (a) : MeasurableSet {y | Q y = a} := by
    have heq : {y | Q y = a} = {y | orbitName T P 4 y = e.symm a} := by
      ext y
      exact e.eq_symm_apply.symm
    rw [heq]
    exact orbitName_measurable_fiber hT.measurable hP 4 _
  have hz := observationEntropyRate_eq_zero_of_measureEntropy μ
    (hT.measurable.iterate 4) hzero Q hQ
  rw [observationEntropyRate_recode μ (T^[4]) (orbitName T P 4) e,
    observationEntropyRate_four_blocks μ hT P hP] at hz
  have hp : observationEntropyRate μ T P = 0 := by linarith
  rw [hp, ENNReal.ofReal_zero]
  exact bot_le

theorem measureEntropy_fourth_iterate_pos {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hpos : 0 < measureEntropy μ T) :
    0 < measureEntropy μ (T^[4]) := by
  by_contra h
  have hz : measureEntropy μ (T^[4]) = 0 := le_antisymm (not_lt.mp h) bot_le
  exact (ne_of_gt hpos) (measureEntropy_eq_zero_of_fourth_iterate μ hT hz)

end DukePrimeDegree

end

end OAI
