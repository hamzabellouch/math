import OAI.NumberTheory.DukePrimeDegree.Entropy.WeylRootInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularRootEntropyLower
import OAI.NumberTheory.DukePrimeDegree.Geometry.RegularRootSymmetry

namespace OAI

/-! # Regular entropy lower bounds and the upper-bound criterion

The expanding-root kernel gives one chamber's lower bound. Weyl
covariance transports it to the opposite chamber. The finite regular
upper estimates therefore imply the entropy identities and coefficient
balance required by prime-degree rigidity.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootEntropyForm_neg_of_monotone {n : ℕ}
    (w : Fin n → Fin n → ℝ) (ell : Fin n → ℝ) (hmono : Monotone ell) :
    rootEntropyForm w (fun i => -ell i) =
      ∑ p : allPositiveRoots n, (ell p.val.2 - ell p.val.1) * w p.val.1 p.val.2 := by
  classical
  rw [← Finset.sum_subtype (allPositiveRoots n) (by intro p; rfl)
    (fun p : Fin n × Fin n => (ell p.2 - ell p.1) * w p.1 p.2)]
  simp only [allPositiveRoots, Finset.sum_filter, Fintype.sum_prod_type, rootEntropyForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [ite_eq_left hij, neg_sub_neg, max_eq_left (sub_nonneg.mpr (hmono hij.le))]
    ring
  · rw [ite_eq_right hij, neg_sub_neg,
      max_eq_right (sub_nonpos.mpr (hmono (le_of_not_gt hij))), mul_zero]

private lemma monotone_of_positive_root_gaps (d : ℕ)
    (ell : Fin (d + 1) → ℝ)
    (hgap : ∀ p : allPositiveRoots (d + 1), Real.log 4 ≤ ell p.val.2 - ell p.val.1) :
    Monotone ell := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · have h := hgap ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
    have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · exact le_rfl

section Measure

variable {d : ℕ} (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]

theorem rootEntropyForm_le_regular_entropy_neg
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (hgap : ∀ p : allPositiveRoots (d + 1), Real.log 4 ≤ ell p.val.2 - ell p.val.1) :
    ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (fun i => -ell i)) ≤
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) := by
  rw [rootEntropyForm_neg_of_monotone _ ell (monotone_of_positive_root_gaps d ell hgap)]
  exact positive_root_sum_le_diagonal_entropy d ell hell hgap μ

/-- The forward-time lower bound uses numeric Weyl transport of the
actual leaf coefficients, not an assumed coefficient symmetry. -/
theorem rootEntropyForm_le_regular_entropy_pos
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (hgap : ∀ p : allPositiveRoots (d + 1), Real.log 4 ≤ ell p.val.2 - ell p.val.1) :
    ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) ell) ≤
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) := by
  let e : Equiv.Perm (Fin (d + 1)) := Fin.revPerm
  let nu := μ.map (quotientReindex e)
  let ellR := fun i => -ell (e.symm i)
  have hsum : ∑ i, ellR i = 0 := by
    simp only [ellR, Finset.sum_neg_distrib, Equiv.sum_comp, hell, neg_zero]
  have hgapR (p : allPositiveRoots (d + 1)) :
      Real.log 4 ≤ ellR p.val.2 - ellR p.val.1 := by
    have hrev : p.val.2.rev < p.val.1.rev :=
      Fin.rev_lt_rev.mpr (Finset.mem_filter.mp p.prop).2
    have h := hgap ⟨(p.val.2.rev, p.val.1.rev),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrev⟩⟩
    simpa only [ellR, e, Fin.revPerm_symm, Fin.revPerm_apply, neg_sub_neg] using h
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) nu :=
    diagonal_ergodic_reindex d e μ
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hform : rootEntropyForm (canonicalRootCoefficient d nu) (fun i => -ellR i) =
      rootEntropyForm (canonicalRootCoefficient d μ) ell := by
    simp only [ellR, neg_neg]
    exact rootEntropyForm_canonical_reindex d e μ hA ell
  have he : diagonalOneParameter ellR hsum (-1) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) 1 := by
    simpa only [ellR, neg_neg] using
      diagonalOneParameter_neg_weights (fun i => ell (e.symm i))
        (permutedWeight_sum e ell hell) (-1)
  have hb := rootEntropyForm_le_regular_entropy_neg nu ellR hsum hgapR
  rw [hform, he] at hb
  exact hb.trans_eq (diagonal_entropy_reindex d e μ ell hell 1)

/-- Both signs of the finite regular tests have their unconditional
root-information lower bound. -/
theorem regular_entropy_tests_lower (a : Option (Fin (d + 1))) :
    ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ≤
        measureEntropy μ (fun x => rightAction x
          (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) ∧
    ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
      (fun i => -regularEntropyTest d a i)) ≤
        measureEntropy μ (fun x => rightAction x
          (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) := by
  have hg (p : allPositiveRoots (d + 1)) :
      Real.log 4 ≤ regularEntropyTest d a p.val.2 - regularEntropyTest d a p.val.1 :=
    regularEntropyTest_gap d a (Finset.mem_filter.mp p.prop).2
  exact ⟨rootEntropyForm_le_regular_entropy_pos μ _ _ hg,
    rootEntropyForm_le_regular_entropy_neg μ _ _ hg⟩

end Measure

/-- The finite regular upper estimates, expressed without entropy identities. -/
def CanonicalRegularEntropyUpperBounds (d : ℕ) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ a : Option (Fin (d + 1)),
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) ≤
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) ≤
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
          (fun i => -regularEntropyTest d a i))

theorem canonicalRegularEntropyTests_of_upper_bounds (d : ℕ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hupper : CanonicalRegularEntropyUpperBounds d μ) :
    CanonicalRegularEntropyTests d μ := by
  intro a
  exact ⟨le_antisymm (hupper a).1 (regular_entropy_tests_lower μ a).1,
    le_antisymm (hupper a).2 (regular_entropy_tests_lower μ a).2⟩

/-- The finite regular upper estimates imply prime-degree entropy rigidity
by the geometric rigidity theorem and both numerical lower bounds. -/
theorem eklPrimeInput_of_regular_entropy_upper_bounds (d : ℕ)
    (hupper : ∀ (μ : Measure (X (d + 1))) (hμ : IsProbabilityMeasure μ),
      ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ →
        @CanonicalRegularEntropyUpperBounds d μ hμ) :
    EKLPrimeInput d := by
  apply eklPrimeInput_of_regular_entropy_tests d
  intro μ hμ hμerg
  let : IsProbabilityMeasure μ := hμ
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ := hμerg
  exact canonicalRegularEntropyTests_of_upper_bounds d μ (hupper μ hμ hμerg)

end DukePrimeDegree

end

end OAI
