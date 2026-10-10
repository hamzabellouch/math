import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularRootEntropyActual
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularRootEntropySandwich

namespace OAI

/-! # The finite regular entropy identities and prime-degree rigidity

The negative-time upper bound uses the actual root-future construction.
Weyl reindexing supplies the positive-time upper bound with the actual
transported leaf coefficients. Together with the proved lower bounds,
these discharge the finite regular tests and the prime-degree EKL input.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

section Measure
variable {d : ℕ} (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]

/-- The actual negative-time entropy is bounded by its canonical root form. -/
theorem regular_entropy_le_root_form_neg
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (fun i => -ell i)) := by
  have hmono : Monotone ell := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have h := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩⟩
      have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith
    · exact le_rfl
  rw [rootEntropyForm_neg_of_monotone _ ell hmono]
  exact negative_diagonal_entropy_le_root_sum d ell hell hgap μ

/-- Reverse the coordinate order and weights to obtain the positive-time
bound without assuming symmetry of opposite root coefficients. -/
theorem regular_entropy_le_root_form_pos
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) ≤
      ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) ell) := by
  let e : Equiv.Perm (Fin (d+1)) := Fin.revPerm
  let nu := μ.map (quotientReindex e)
  let ellR := fun i => -ell (e.symm i)
  have hsum : ∑ i, ellR i=0 := by
    simp only [ellR,Finset.sum_neg_distrib,Equiv.sum_comp,hell,neg_zero]
  have hgapR (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ ellR p.val.2-ellR p.val.1 := by
    have hrev : p.val.2.rev < p.val.1.rev :=
      Fin.rev_lt_rev.mpr (Finset.mem_filter.mp p.prop).2
    have h := hgap ⟨(p.val.2.rev,p.val.1.rev),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrev⟩⟩
    simpa only [ellR,e,Fin.revPerm_symm,Fin.revPerm_apply,neg_sub_neg] using h
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) nu :=
    diagonal_ergodic_reindex d e μ
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hform : rootEntropyForm (canonicalRootCoefficient d nu) (fun i => -ellR i) =
      rootEntropyForm (canonicalRootCoefficient d μ) ell := by
    simp only [ellR,neg_neg]
    exact rootEntropyForm_canonical_reindex d e μ hA ell
  have he : diagonalOneParameter ellR hsum (-1) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) 1 := by
    simpa only [ellR,neg_neg] using
      diagonalOneParameter_neg_weights (fun i => ell (e.symm i))
        (permutedWeight_sum e ell hell) (-1)
  have hb := regular_entropy_le_root_form_neg nu ellR hsum hgapR
  rw [hform,he] at hb
  exact (diagonal_entropy_reindex d e μ ell hell 1).symm.trans_le hb

/-- Both finite families of regular upper bounds hold without
additional entropy or leaf-measure hypotheses. -/
theorem canonicalRegularEntropyUpperBounds_proved : CanonicalRegularEntropyUpperBounds d μ := by
  intro a
  have hg (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ regularEntropyTest d a p.val.2-regularEntropyTest d a p.val.1 :=
    regularEntropyTest_gap d a (Finset.mem_filter.mp p.prop).2
  exact ⟨regular_entropy_le_root_form_pos μ _ _ hg,
    regular_entropy_le_root_form_neg μ _ _ hg⟩

/-- Exact regular entropy identities, using the intrinsic coefficients. -/
theorem canonicalRegularEntropyTests_proved : CanonicalRegularEntropyTests d μ :=
  canonicalRegularEntropyTests_of_upper_bounds d μ (canonicalRegularEntropyUpperBounds_proved μ)

/-- The actual invariant-root relation is symmetric. -/
theorem rootInvarianceRelation_symmetric_proved (hd : 2 < d+1) :
    Std.Symm (rootInvarianceRelation μ) :=
  rootInvarianceRelation_symmetric_of_regular_tests hd (canonicalRegularEntropyTests_proved μ)

/-- Positive regular entropy forces Haar probability in prime degree. -/
theorem isHaar_of_prime_positive_regular_entropy (hprime : (d+1).Prime) (hd : 2 < d+1)
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    IsHaarProbability μ :=
  isHaar_of_prime_regular_entropy_tests hprime hd (canonicalRegularEntropyTests_proved μ) hpos

end Measure

/-- The published rigidity specialization required by the packet proof,
with all its mathematical input proved for this application. -/
theorem eklPrimeInput_unconditional (d : ℕ) : EKLPrimeInput d := by
  apply eklPrimeInput_of_regular_entropy_upper_bounds d
  intro μ hμ hμerg
  let : IsProbabilityMeasure μ := hμ
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ := hμerg
  exact canonicalRegularEntropyUpperBounds_proved μ

end DukePrimeDegree

end

end OAI
