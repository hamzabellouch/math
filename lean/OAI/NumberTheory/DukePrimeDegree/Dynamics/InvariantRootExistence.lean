import OAI.NumberTheory.DukePrimeDegree.Dynamics.NoInvariantRootGraph
import OAI.NumberTheory.DukePrimeDegree.Entropy.ZeroEntropyAllRoots
import OAI.NumberTheory.DukePrimeDegree.Geometry.AtomicRootPositivity

namespace OAI

/-! # Positive entropy yields an invariant root without the numerical entropy formula -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Commutators, isolated-root shearing, a source ordering, and the
zero-entropy criterion suffice for existence of one invariant root.
No numerical entropy identity or homogeneous-orbit hypothesis is used. -/
theorem exists_invariant_root_of_positive_regular_entropy
    (d : ℕ) (hd : 2 < d+1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    ∃ (i j : Fin (d+1)) (hij : i ≠ j), ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t))=μ := by
  classical
  by_contra hn
  have hnone : ∀ (i j : Fin (d+1)) (hij : i ≠ j), ¬ ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t))=μ := by
    intro i j hij ht
    exact hn ⟨i,j,hij,ht⟩
  obtain ⟨e,he⟩ := exists_source_order (d+1)
    (fun i j => 0 < canonicalRootCoefficient d μ i j)
    (no_two_step_positive_roots_of_no_invariant_root d hd μ hnone)
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  let ν := μ.map (quotientReindex e)
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) ν :=
    diagonal_ergodic_reindex d e μ
  have hAν (u : LogCoordinates d) : ν.map (fun x => rightAction x (diagonalFlow u))=ν :=
    diagonal_invariant_reindex d e μ hA u
  have hatom (p : ↥(allPositiveRoots (d+1) \ ∅)) : ∀ᵐ x ∂ν,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) ν x=
        Measure.dirac 0 := by
    have hp : p.val.1 < p.val.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
    have hij : e.symm p.val.1 ≠ e.symm p.val.2 := e.symm.injective.ne (ne_of_lt hp)
    have hz : canonicalRootCoefficient d μ (e.symm p.val.1) (e.symm p.val.2)=0 := by
      apply le_antisymm _ (canonicalRootCoefficient_nonneg d μ _ _)
      apply le_of_not_gt
      intro h
      have hh := he _ _ h
      simp only [Equiv.apply_symm_apply] at hh
      exact (lt_asymm hp hh)
    have ha := (canonicalRootCoefficient_zero_iff d μ hA _ _ hij).mp hz
    have H := atomic_root_reindex d e hij μ hA ha
    simpa only [Equiv.apply_symm_apply] using H
  have hgap (p : allPositiveRoots (d+1)) : Real.log 4 ≤
      regularEntropyTest d none p.val.2-regularEntropyTest d none p.val.1 :=
    regularEntropyTest_gap d none (Finset.mem_filter.mp p.prop).2
  have hzero := diagonal_entropy_zero_of_atomic_positive_roots d
    (regularEntropyTest d none) (regularEntropyTest_sum d none) hgap ν hatom
  have hall := all_roots_atomic_of_zero_regular_entropy d
    (regularEntropyTest d none) (regularEntropyTest_sum d none) hgap ν hzero
  have hm : ν.map (quotientReindex e.symm)=μ := by
    change (μ.map (quotientReindex e)).map (quotientReindex e.symm)=μ
    rw [Measure.map_map (continuous_quotientReindex e.symm).measurable
      (continuous_quotientReindex e).measurable]
    have hid : quotientReindex e.symm ∘ quotientReindex e=id := by
      funext x
      exact quotientReindex_symm_apply e x
    rw [hid,Measure.map_id]
  obtain ⟨i,j,hij,hp⟩ := positive_root_coefficient_of_regular_entropy d μ hpos
  have ha := atomic_root_reindex d e.symm (e.injective.ne (ne_of_lt hij)) ν hAν
    (hall (e i) (e j) (e.injective.ne (ne_of_lt hij)))
  have ha' : ∀ᵐ x ∂μ, intrinsicRootLeaf (ne_of_lt hij) μ x=Measure.dirac 0 := by
    simpa only [hm,Equiv.symm_apply_apply] using ha
  exact hp.ne' ((canonicalRootCoefficient_zero_iff d μ hA i j (ne_of_lt hij)).mpr ha')

end DukePrimeDegree

end

end OAI
