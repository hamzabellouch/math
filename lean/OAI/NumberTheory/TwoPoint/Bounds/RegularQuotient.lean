import OAI.NumberTheory.TwoPoint.Bounds.MaximalPairs
import OAI.NumberTheory.TwoPoint.Walks.IncidenceForest

namespace OAI

/-! The low-rank hypothesis produces the regular quotient directions used in forest coding. -/

namespace TwoPointCorrelations

open Finset Submodule

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]
  [DecidableEq α] [DecidableEq ι]

/-- All pairs of departures carrying the same label. A caller may restrict
`ι` to the lit occurrences before applying this construction. -/
def EqualLabelPairs (label : ι → α) :=
  {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1}

instance equalLabelPairsFintype (label : ι → α) : Fintype (EqualLabelPairs label) :=
  inferInstanceAs (Fintype {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1})

instance equalLabelPairsDecidableEq (label : ι → α) : DecidableEq (EqualLabelPairs label) :=
  inferInstanceAs (DecidableEq {p : α × ι × ι // label p.2.1 = p.1 ∧ label p.2.2 = p.1})

/-- Difference first, coordinate direction second, so the generic maximal
pair theorem applies without reordering the joint independent family. -/
noncomputable def labelPairVectors (label : ι → α) (offset : ι → α → K)
    (p : EqualLabelPairs label) : Fin 2 → (α → K) :=
  ![offset p.val.2.1 - offset p.val.2.2, Pi.basisFun K α p.val.1]

/-- The algebraic part of forest coding: fewer than `r` independent pairs
leave fewer than `2r` omitted labels; all remaining departures for a label
lie along its independent coordinate direction in the quotient. -/
theorem exists_regular_quotient (label : ι → α) (offset : ι → α → K) (r : ℕ)
    (hno : ∀ S : Finset (EqualLabelPairs label), S.card = r →
      ¬LinearIndependent K (pairFamily (labelPairVectors label offset) S)) :
    ∃ (D : Submodule K (α → K)) (R : Finset α), Rᶜ.card < 2 * r ∧
      LinearIndependent K (fun z : R => D.mkQ (Pi.basisFun K α z)) ∧
      span K (Set.range (fun z : R => D.mkQ (Pi.basisFun K α z))) = ⊤ ∧
      ∀ (z : R) i j, label i = z → label j = z →
        ∃ c : K, D.mkQ (offset i) = D.mkQ (offset j) +
          c • D.mkQ (Pi.basisFun K α z) := by
  classical
  let v := labelPairVectors label offset
  obtain ⟨S, hcard, hind, hdim, hmax⟩ := exists_small_maximal_independent_pairs v r hno
  let D := span K (Set.range (pairFamily v S))
  obtain ⟨R, hRcard, hRind, hRspan⟩ := exists_coordinate_quotient_basis D
  refine ⟨D, R, ?_, hRind, hRspan, ?_⟩
  · rw [hRcard, hdim]
    omega
  · intro z i j hi hj
    let p : EqualLabelPairs label := ⟨(z, i, j), hi, hj⟩
    have hx : D.mkQ (v p 1) ≠ 0 := by
      exact hRind.ne_zero z
    have hpS : p ∉ S := by
      intro hp
      apply hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact subset_span ⟨(⟨p, hp⟩, 1), rfl⟩
    have hpv : v p = ![offset i - offset j, Pi.basisFun K α z] := rfl
    obtain ⟨c, hc⟩ := quotient_line_of_nonextendable_pair (pairFamily v S) hind
      (Pi.basisFun K α z) (offset i - offset j) hx
      (by simpa only [← hpv] using hmax p hpS)
    refine ⟨c, ?_⟩
    rw [map_sub] at hc
    exact sub_eq_iff_eq_add'.mp hc

end TwoPointCorrelations

end OAI
