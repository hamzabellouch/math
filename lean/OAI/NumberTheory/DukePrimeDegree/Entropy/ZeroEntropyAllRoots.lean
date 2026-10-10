import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularRootEntropyLower
import OAI.NumberTheory.DukePrimeDegree.Dynamics.WeylAtomicRoots
import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylDiagonalAction

namespace OAI

/-! # A zero-entropy regular element has atomic leaves in both root directions -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma atomic_positive_root_of_zero_entropy (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hz : measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0)
    {i j : Fin (d+1)} (hij : i < j) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf (ne_of_lt hij) μ x=Measure.dirac 0 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  exact (canonicalRootCoefficient_zero_iff d μ hA i j (ne_of_lt hij)).mp
    ((diagonal_entropy_zero_iff_positive_coefficients_zero d ell hell hgap μ).mp hz
      ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩)

/-- Time reversal gives zero entropy in the opposite chamber. Reindexing
that chamber lets the same proved positive-root lower bound apply there. -/
theorem all_roots_atomic_of_zero_regular_entropy (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hz : measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0) :
    ∀ (i j : Fin (d+1)) (hij : i ≠ j), ∀ᵐ x ∂μ,
      intrinsicRootLeaf hij μ x=Measure.dirac 0 := by
  let e : Equiv.Perm (Fin (d+1)) := Fin.revPerm
  let ν := μ.map (quotientReindex e)
  let ellR := fun i => -ell (e.symm i)
  have hsum : ∑ i, ellR i=0 := by
    simp only [ellR,Finset.sum_neg_distrib,Equiv.sum_comp,hell,neg_zero]
  have hgapR (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ ellR p.val.2-ellR p.val.1 := by
    have hrev : p.val.2.rev < p.val.1.rev :=
      Fin.rev_lt_rev.mpr (Finset.mem_filter.mp p.prop).2
    have hh := hgap ⟨(p.val.2.rev,p.val.1.rev),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrev⟩⟩
    simpa only [ellR,e,Fin.revPerm_symm,Fin.revPerm_apply,neg_sub_neg] using hh
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) ν :=
    diagonal_ergodic_reindex d e μ
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hAν (u : LogCoordinates d) : ν.map (fun x => rightAction x (diagonalFlow u))=ν :=
    diagonal_invariant_reindex d e μ hA u
  have hp0 : measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1))=0 :=
    (diagonal_entropy_neg d ell hell μ hA 1).symm.trans hz
  have he : diagonalOneParameter ellR hsum (-1) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) 1 := by
    simpa only [neg_neg] using
      diagonalOneParameter_neg_weights (fun i => ell (e.symm i))
        (permutedWeight_sum e ell hell) (-1)
  have hzν : measureEntropy ν (fun x => rightAction x (diagonalOneParameter ellR hsum (-1)))=0 := by
    rw [he]
    exact (diagonal_entropy_reindex d e μ ell hell 1).trans hp0
  have hm : ν.map (quotientReindex e.symm)=μ := by
    change (μ.map (quotientReindex e)).map (quotientReindex e.symm)=μ
    rw [Measure.map_map (continuous_quotientReindex e.symm).measurable
      (continuous_quotientReindex e).measurable]
    have hid : quotientReindex e.symm ∘ quotientReindex e=id := by
      funext x
      exact quotientReindex_symm_apply e x
    rw [hid,Measure.map_id]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact atomic_positive_root_of_zero_entropy d ell hell hgap μ hz hijlt
  · have hrev : e i < e j := by
      change i.rev < j.rev
      exact Fin.rev_lt_rev.mpr hjilt
    have ha := atomic_positive_root_of_zero_entropy d ellR hsum hgapR ν hzν hrev
    have ht := atomic_root_reindex d e.symm (e.injective.ne hij) ν hAν ha
    simpa only [hm,Equiv.symm_apply_apply] using ht

end DukePrimeDegree

end

end OAI
