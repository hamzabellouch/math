import OAI.Probability.SATComputability.RootEnergy
import OAI.Probability.RandomSAT.Transfer
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem finiteClauseAverage_iterate {n m : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (S : Finset (Assignment n)) :
    ((finiteClauseAverage sat)^[m] alive) S =
      uniformMean (fun F : Fin m → C => alive (S.filter (fun s => ∀ j, sat (F j) s))) := by
  induction m generalizing S with
  | zero =>
    simp only [Function.iterate_zero_apply, Fin.forall_fin_zero, Finset.filter_true]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', finiteClauseAverage, uniformMean_fin_succ]
    apply uniformMean_congr
    intro c
    rw [ih]
    apply uniformMean_congr
    intro F
    congr 1
    ext s
    simp only [Finset.mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    tauto

def relaxedClauseEquiv (n : ℕ) : RelaxedClause n ≃ AuxiliaryClause n 3 where
  toFun c j := (c.1 j, c.2 j)
  invFun c := (fun j => (c j).1, fun j => (c j).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem relaxedClauseEquiv_satisfies {n : ℕ} (c : RelaxedClause n) (s : Assignment n) :
    auxiliarySatisfies s (relaxedClauseEquiv n c) ↔
      relaxedClauseSatisfied s c.1 c.2 := by
  rfl

theorem clauseMinimum_zero_iff {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs = 0 ↔ ∃ s : Assignment n, ∀ j,
      relaxedClauseSatisfied s (cs j).1 (cs j).2 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
    refine ⟨s, ?_⟩
    change relaxedViolations s _ _ = clauseMinimum cs at hs
    rw [h] at hs
    simpa only [relaxedViolations, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_not] using hs
  · rintro ⟨s, hs⟩
    have h := relaxedMinimum_le (fun j => (cs j).1) (fun j => (cs j).2) s
    have hz : relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) = 0 := by
      simp only [relaxedViolations, hs, not_true_eq_false, Finset.filter_false,
        Finset.card_empty]
    exact Nat.eq_zero_of_le_zero (hz ▸ h)

theorem auxiliaryProbability_eq_minimum (n m : ℕ) :
    auxiliaryProbability n 3 m =
      uniformMean (fun cs : Fin m → RelaxedClause n =>
        if clauseMinimum cs = 0 then 1 else 0) := by
  unfold auxiliaryProbability auxiliarySurvival auxiliaryAverage embeddedAverage
  rw [finiteClauseAverage_iterate]
  let e := Equiv.piCongrRight (fun _ : Fin m => relaxedClauseEquiv n)
  rw [← uniformMean_equiv e]
  apply uniformMean_congr
  intro cs
  unfold alive
  congr 1
  apply propext
  rw [clauseMinimum_zero_iff]
  simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
  rfl

theorem integral_rootMinimum_zero (n m : ℕ) [NeZero n] :
    (∫ x : RootPath (RelaxedClause n) m,
      (if rootMinimum n m x = 0 then (1 : ℝ) else 0)
      ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = auxiliaryProbability n 3 m := by
  rw [auxiliaryProbability_eq_minimum]
  change (∫ x, (if (clauseMinimum (rootArray m x) : ℝ) = 0 then (1 : ℝ) else 0)
    ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = _
  simp only [Nat.cast_eq_zero]
  rw [integral_rootArray_eq_pi (finiteUniform (RelaxedClause n)) m
    (fun cs => if clauseMinimum cs = 0 then (1 : ℝ) else 0),
    finiteUniform_pi, integral_finiteUniform]
  simp only [uniformMean, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem rootSatisfiableProbability_eq_auxiliary (n : ℕ) [NeZero n] (r : ℝ≥0) :
    rootSatisfiableProbability n (finiteUniform (RelaxedClause n)) r =
      ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure r := by
  unfold rootSatisfiableProbability poissonRootAverage rootAverage
  simp only [integral_rootMinimum_zero]

noncomputable def relaxedFixedMinimum (n m : ℕ) : ℝ :=
  uniformMean (fun cs : Fin m → RelaxedClause n => (clauseMinimum cs : ℝ))

noncomputable def relaxedPoissonMinimum (n : ℕ) (a : ℝ≥0) : ℝ :=
  ∫ m : ℕ, relaxedFixedMinimum n m ∂poissonMeasure (a*n)

theorem relaxedFixedMinimum_nonneg (n m : ℕ) : 0 ≤ relaxedFixedMinimum n m :=
  uniformMean_nonneg (fun _ => Nat.cast_nonneg _)

theorem relaxedFixedMinimum_le (n m : ℕ) [NeZero n] : relaxedFixedMinimum n m ≤ m := by
  calc
    _ ≤ uniformMean (fun _cs : Fin m → RelaxedClause n => (m : ℝ)) :=
      uniformMean_mono (fun cs => by exact_mod_cast clauseMinimum_le_length cs)
    _ = _ := uniformMean_const _

theorem relaxedPoissonMinimum_nonneg (n : ℕ) (a : ℝ≥0) :
    0 ≤ relaxedPoissonMinimum n a := integral_nonneg (fun _ => relaxedFixedMinimum_nonneg _ _)

theorem integral_rootMinimum_eq (n m : ℕ) [NeZero n] :
    (∫ x : RootPath (RelaxedClause n) m, rootMinimum n m x
      ∂rootLaw m (fun _ => finiteUniform (RelaxedClause n))) = relaxedFixedMinimum n m := by
  simp only [rootMinimum]
  rw [integral_rootArray_eq_pi (finiteUniform (RelaxedClause n)) m
    (fun cs => (clauseMinimum cs : ℝ)), finiteUniform_pi, integral_finiteUniform]
  simp only [relaxedFixedMinimum, uniformMean, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem poissonRootAverage_minimum_eq (n : ℕ) [NeZero n] (a : ℝ≥0) :
    poissonRootAverage (finiteUniform (RelaxedClause n)) (a*n) (rootMinimum n) =
      relaxedPoissonMinimum n a := by
  unfold poissonRootAverage rootAverage relaxedPoissonMinimum
  simp only [integral_rootMinimum_eq]

end FixedClauseThreshold.Computability

end OAI
