import OAI.Probability.InvariantIsing.Arrays.TensorWardCorrectionBound
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Finite Ward terms expressed as ordinary reference-replica observables.
These identities prepare countable leaf exhaustion without differentiating
an infinite Gibbs integral. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma referenceReplicaMean_finiteGibbs (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) {r : ℕ} (D : (Fin r → S) → ℝ) :
    referenceReplicaMean ν H D =
      ∑ σ, (∏ i, finiteGibbs (fun s => ν.real {s}) H (σ i)) * D σ := by
  rw [referenceReplicaMean_finite]
  simp only [finiteGibbs, finitePartition, referencePartition_finite]

lemma referenceReplicaMean_one (ν : Measure S) [IsProbabilityMeasure ν]
    (H O : S → ℝ) :
    referenceReplicaMean ν H (fun σ : Fin 1 → S => O (σ 0)) =
      gibbsAverage (fun s => ν.real {s}) H O := by
  rw [referenceReplicaMean_finiteGibbs,
    ← Equiv.sum_comp (Equiv.funUnique (Fin 1) S).symm]
  simp only [Fin.prod_univ_one, Equiv.funUnique_symm_apply, gibbsAverage]
  rfl

lemma referenceReplicaMean_two (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) (O : S → S → ℝ) :
    referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) (σ 1)) =
      gibbsPairAverage (fun s => ν.real {s}) H O := by
  rw [referenceReplicaMean_finiteGibbs,
    ← Equiv.sum_comp (finTwoArrowEquiv S).symm, Fintype.sum_prod_type]
  simp only [Fin.prod_univ_two, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, gibbsPairAverage]

lemma referenceReplicaMean_three (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) (O : S → S → S → ℝ) :
    referenceReplicaMean ν H (fun σ : Fin 3 → S => O (σ 0) (σ 1) (σ 2)) =
      gibbsTripleAverage (fun s => ν.real {s}) H O := by
  rw [referenceReplicaMean_finiteGibbs,
    ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 3 => S)), Fintype.sum_prod_type]
  unfold gibbsTripleAverage
  apply Finset.sum_congr rfl
  intro s _
  rw [← Equiv.sum_comp (finTwoArrowEquiv S).symm, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  simp only [Fin.prod_univ_zero, mul_one]
  change finiteGibbs (fun s => ν.real {s}) H s *
      (finiteGibbs (fun s => ν.real {s}) H t * finiteGibbs (fun s => ν.real {s}) H u) * O s t u = _
  ring

lemma finiteGibbsVariation_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H O A dO : S → ℝ) :
    finiteGibbsVariation (fun s => ν.real {s}) H O A dO =
      referenceReplicaMean ν H (fun σ : Fin 1 → S => dO (σ 0) + O (σ 0) * A (σ 0)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) * A (σ 1)) := by
  rw [referenceReplicaMean_one ν H (fun s => dO s + O s * A s),
    referenceReplicaMean_two ν H (fun s t => O s * A t)]
  simp only [finiteGibbsVariation, gibbsAverage, gibbsPairAverage,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- A pair-state derivative reduces to two- and three-replica averages
under the original state prior. -/
lemma finiteGibbsVariation_pair_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H A : S → ℝ) (O dO : S → S → ℝ) :
    finiteGibbsVariation (fun p : S × S => ν.real {p.1} * ν.real {p.2})
      (fun p => H p.1 + H p.2) (fun p => O p.1 p.2)
      (fun p => A p.1 + A p.2) (fun p => dO p.1 p.2) =
      referenceReplicaMean ν H (fun σ : Fin 2 → S =>
        dO (σ 0) (σ 1) + O (σ 0) (σ 1) * (A (σ 0) + A (σ 1))) -
      2 * referenceReplicaMean ν H (fun σ : Fin 3 → S => O (σ 0) (σ 1) * A (σ 2)) := by
  rw [referenceReplicaMean_two ν H (fun s t => dO s t + O s t * (A s + A t)),
    referenceReplicaMean_three ν H (fun s t u => O s t * A u)]
  unfold finiteGibbsVariation
  rw [gibbsAverage_pair (fun s => ν.real {s}) H dO,
    gibbsAverage_pair (fun s => ν.real {s}) H (fun s t => O s t * (A s + A t)),
    gibbsAverage_pair (fun s => ν.real {s}) H O,
    gibbsAverage_pair_sum (finite_reference_GibbsReference ν) H A,
    gibbsPairAverage_add]
  rw [show gibbsPairAverage (fun s => ν.real {s}) H O *
      (2 * gibbsAverage (fun s => ν.real {s}) H A) =
      2 * (gibbsPairAverage (fun s => ν.real {s}) H O *
        gibbsAverage (fun s => ν.real {s}) H A) by ring,
    gibbsPairAverage_mul_gibbsAverage]

lemma gaussianWardCorrection_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H O : S → ℝ) (K : S → S → ℝ) :
    gaussianWardCorrection (fun s => ν.real {s}) H O K =
      referenceReplicaMean ν H (fun σ : Fin 1 → S => O (σ 0) * K (σ 0) (σ 0)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) * K (σ 0) (σ 1)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) * (K (σ 1) (σ 0) + K (σ 1) (σ 1))) +
      2 * referenceReplicaMean ν H (fun σ : Fin 3 → S => O (σ 0) * K (σ 1) (σ 2)) := by
  rw [referenceReplicaMean_one ν H (fun s => O s * K s s),
    referenceReplicaMean_two ν H (fun s t => O s * K s t),
    referenceReplicaMean_two ν H (fun s t => O s * (K t s + K t t)),
    referenceReplicaMean_three ν H (fun s t u => O s * K t u)]
  rfl

lemma gibbsKernelCorrection_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) (C : S → S → S → ℝ) :
    gibbsKernelCorrection (fun s => ν.real {s}) H C =
      referenceReplicaMean ν H (fun σ : Fin 1 → S => C (σ 0) (σ 0) (σ 0)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => C (σ 0) (σ 0) (σ 1)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => C (σ 0) (σ 1) (σ 0) + C (σ 0) (σ 1) (σ 1)) +
      2 * referenceReplicaMean ν H (fun σ : Fin 3 → S => C (σ 0) (σ 1) (σ 2)) := by
  rw [referenceReplicaMean_one ν H (fun s => C s s s),
    referenceReplicaMean_two ν H (fun s t => C s s t),
    referenceReplicaMean_two ν H (fun s t => C s t s + C s t t),
    referenceReplicaMean_three ν H C]
  rfl

/-- Pair-state Gaussian corrections can be exhausted on the product prior
without expanding them into six individually named replicas. -/
lemma gibbsKernelCorrection_pair_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S × S → ℝ) (C : (S × S) → (S × S) → (S × S) → ℝ) :
    gibbsKernelCorrection (fun p : S × S => ν.real {p.1} * ν.real {p.2}) H C =
      referenceReplicaMean (ν.prod ν) H (fun σ : Fin 1 → S × S => C (σ 0) (σ 0) (σ 0)) -
      referenceReplicaMean (ν.prod ν) H (fun σ : Fin 2 → S × S => C (σ 0) (σ 0) (σ 1)) -
      referenceReplicaMean (ν.prod ν) H
        (fun σ : Fin 2 → S × S => C (σ 0) (σ 1) (σ 0) + C (σ 0) (σ 1) (σ 1)) +
      2 * referenceReplicaMean (ν.prod ν) H (fun σ : Fin 3 → S × S => C (σ 0) (σ 1) (σ 2)) := by
  have hw : (fun p : S × S => ν.real {p.1} * ν.real {p.2}) = fun p => (ν.prod ν).real {p} := by
    funext p
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod]
  rw [hw]
  exact gibbsKernelCorrection_reference (ν.prod ν) H C

end InvariantIsing

end

end OAI
