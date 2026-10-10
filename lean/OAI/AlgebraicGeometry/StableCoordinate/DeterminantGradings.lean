import OAI.AlgebraicGeometry.StableCoordinate.HomogeneousQuotient
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

namespace OAI

/-!
# The two actual integer gradings on the determinant hypersurface

The degrees are exactly the two rows in source equation `rig:gradings`.
Both gradings are constructed on `C = k[a,d,b,c,u]/(ac-bd-1)` by quotienting
weighted polynomial gradings.  In particular, negative auxiliary and fiber
degrees are retained.
-/

noncomputable section

namespace StableCoordinate.Obstruction

open MvPolynomial

variable (k : Type*) [CommRing k]

/-- The weighted pieces on the five-variable polynomial presentation. -/
abbrev polynomialPiece (w : Fin 5 → ℤ) : ℤ → Submodule k (P k 5) :=
  MvPolynomial.weightedHomogeneousSubmodule k w

instance polynomialGrading (w : Fin 5 → ℤ) : GradedAlgebra (polynomialPiece k w) :=
  MvPolynomial.weightedGradedAlgebra k w

/-- The determinant relation is homogeneous whenever the products `ac` and
`bd` both have degree zero. -/
theorem determinantRelation_homogeneous (w : Fin 5 → ℤ)
    (hac : w 0 + w 3 = 0) (hbd : w 2 + w 1 = 0) :
    determinantRelation k ∈ polynomialPiece k w 0 := by
  have hac' : (X 0 * X 3 : P k 5) ∈ polynomialPiece k w 0 := by
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    simpa only [hac] using
      (MvPolynomial.isWeightedHomogeneous_X k w 0).mul
        (MvPolynomial.isWeightedHomogeneous_X k w 3)
  have hbd' : (X 2 * X 1 : P k 5) ∈ polynomialPiece k w 0 := by
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    simpa only [hbd] using
      (MvPolynomial.isWeightedHomogeneous_X k w 2).mul
        (MvPolynomial.isWeightedHomogeneous_X k w 1)
  exact (polynomialPiece k w 0).sub_mem ((polynomialPiece k w 0).sub_mem hac' hbd')
    (MvPolynomial.isWeightedHomogeneous_one k w)

/-- Thus the whole defining ideal is homogeneous, not just its displayed generator. -/
theorem idealC_homogeneous (w : Fin 5 → ℤ)
    (hac : w 0 + w 3 = 0) (hbd : w 2 + w 1 = 0) :
    (idealC k).IsHomogeneous (polynomialPiece k w) := by
  apply Ideal.homogeneous_span
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact ⟨0, determinantRelation_homogeneous k w hac hbd⟩

/-- The induced weighted pieces in the determinant quotient. -/
abbrev determinantPiece (w : Fin 5 → ℤ) : ℤ → Submodule k (C k) :=
  HomogeneousQuotient.piece (polynomialPiece k w) (idealC k)

/-- The quotient grading for any weight vector satisfying the two determinant constraints. -/
@[implicit_reducible]
def determinantGrading (w : Fin 5 → ℤ)
    (hac : w 0 + w 3 = 0) (hbd : w 2 + w 1 = 0) :
    GradedAlgebra (determinantPiece k w) :=
  HomogeneousQuotient.gradedAlgebra (polynomialPiece k w) (idealC k)
    (idealC_homogeneous k w hac hbd)

/-- Actual auxiliary homogeneous pieces: `deg(a,d,b,c,u) = (0,1,-1,0,1)`. -/
abbrev auxiliaryPiece : ℤ → Submodule k (C k) := determinantPiece k auxiliaryWeight
/-- Actual fiber-weight pieces: `wt(a,d,b,c,u) = (1,1,-1,-1,0)`. -/
abbrev fiberPiece : ℤ → Submodule k (C k) := determinantPiece k fiberWeight

instance auxiliaryGrading : GradedAlgebra (auxiliaryPiece k) :=
  determinantGrading k auxiliaryWeight (by decide) (by decide)

instance fiberGrading : GradedAlgebra (fiberPiece k) :=
  determinantGrading k fiberWeight (by decide) (by decide)

/-- Every generator has its assigned auxiliary degree. -/
theorem cX_mem_auxiliaryPiece (i : Fin 5) : cX k i ∈ auxiliaryPiece k (auxiliaryWeight i) :=
  HomogeneousQuotient.mk_mem_piece (polynomialPiece k auxiliaryWeight) (idealC k)
    (MvPolynomial.isWeightedHomogeneous_X k auxiliaryWeight i)

/-- Every generator has its assigned fiber weight. -/
theorem cX_mem_fiberPiece (i : Fin 5) : cX k i ∈ fiberPiece k (fiberWeight i) :=
  HomogeneousQuotient.mk_mem_piece (polynomialPiece k fiberWeight) (idealC k)
    (MvPolynomial.isWeightedHomogeneous_X k fiberWeight i)

/-- The degree-minus-one part of the obstruction polynomial. -/
def vLow : C k := cX k 0 ^ 3 * cX k 2
/-- The degree-two part of the obstruction polynomial. -/
def vHigh : C k := cX k 0 ^ 2 * cX k 4 ^ 2 - cX k 1 ^ 2

theorem v_eq_low_add_high : v k = vLow k + vHigh k := by
  simp only [v, vLow, vHigh, add_sub_assoc]

/-- The lower term of `v` has auxiliary degree minus one. -/
theorem vLow_mem_auxiliaryPiece : vLow k ∈ auxiliaryPiece k (-1) := by
  simpa [auxiliaryWeight, vLow] using
    SetLike.mul_mem_graded (SetLike.pow_mem_graded 3 (cX_mem_auxiliaryPiece k 0))
      (cX_mem_auxiliaryPiece k 2)

/-- The difference of squares in `v` has auxiliary degree two. -/
theorem vHigh_mem_auxiliaryPiece : vHigh k ∈ auxiliaryPiece k 2 := by
  have hau : cX k 0 ^ 2 * cX k 4 ^ 2 ∈ auxiliaryPiece k 2 := by
    simpa [auxiliaryWeight] using
      SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 (cX_mem_auxiliaryPiece k 0))
        (SetLike.pow_mem_graded 2 (cX_mem_auxiliaryPiece k 4))
  have hd : cX k 1 ^ 2 ∈ auxiliaryPiece k 2 := by
    simpa [auxiliaryWeight] using SetLike.pow_mem_graded 2 (cX_mem_auxiliaryPiece k 1)
  exact (auxiliaryPiece k 2).sub_mem hau hd

/-- Both auxiliary parts have fiber weight two. -/
theorem vLow_mem_fiberPiece : vLow k ∈ fiberPiece k 2 := by
  simpa [fiberWeight, vLow] using
    SetLike.mul_mem_graded (SetLike.pow_mem_graded 3 (cX_mem_fiberPiece k 0))
      (cX_mem_fiberPiece k 2)

theorem vHigh_mem_fiberPiece : vHigh k ∈ fiberPiece k 2 := by
  have hau : cX k 0 ^ 2 * cX k 4 ^ 2 ∈ fiberPiece k 2 := by
    simpa [fiberWeight] using
      SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 (cX_mem_fiberPiece k 0))
        (SetLike.pow_mem_graded 2 (cX_mem_fiberPiece k 4))
  have hd : cX k 1 ^ 2 ∈ fiberPiece k 2 := by
    simpa [fiberWeight] using SetLike.pow_mem_graded 2 (cX_mem_fiberPiece k 1)
  exact (fiberPiece k 2).sub_mem hau hd

/-- The full obstruction polynomial is homogeneous of fiber weight two. -/
theorem v_mem_fiberPiece : v k ∈ fiberPiece k 2 := by
  rw [v_eq_low_add_high]
  exact (fiberPiece k 2).add_mem (vLow_mem_fiberPiece k) (vHigh_mem_fiberPiece k)

/-- Its auxiliary degree-two projection is exactly the source's difference of squares. -/
@[simp]
theorem auxiliary_proj_v_two :
    GradedAlgebra.proj (auxiliaryPiece k) 2 (v k) = vHigh k := by
  rw [v_eq_low_add_high, map_add]
  have hl : GradedAlgebra.proj (auxiliaryPiece k) 2 (vLow k) = 0 :=
    DirectSum.decompose_of_mem_ne (auxiliaryPiece k) (vLow_mem_auxiliaryPiece k) (by decide)
  have hh : GradedAlgebra.proj (auxiliaryPiece k) 2 (vHigh k) = vHigh k :=
    DirectSum.decompose_of_mem_same (auxiliaryPiece k) (vHigh_mem_auxiliaryPiece k)
  rw [hl, hh, zero_add]

/-- No other auxiliary degrees occur beyond the two explicitly listed parts. -/
theorem auxiliary_proj_v_eq_zero (n : ℤ) (hnlow : (-1 : ℤ) ≠ n) (hnhigh : (2 : ℤ) ≠ n) :
    GradedAlgebra.proj (auxiliaryPiece k) n (v k) = 0 := by
  rw [v_eq_low_add_high, map_add]
  have hl : GradedAlgebra.proj (auxiliaryPiece k) n (vLow k) = 0 :=
    DirectSum.decompose_of_mem_ne (auxiliaryPiece k) (vLow_mem_auxiliaryPiece k) hnlow
  have hh : GradedAlgebra.proj (auxiliaryPiece k) n (vHigh k) = 0 :=
    DirectSum.decompose_of_mem_ne (auxiliaryPiece k) (vHigh_mem_auxiliaryPiece k) hnhigh
  rw [hl, hh, zero_add]

/-- Auxiliary projections commute with passage to the quotient. -/
@[simp]
theorem auxiliary_proj_mk (n : ℤ) (p : P k 5) :
    GradedAlgebra.proj (auxiliaryPiece k) n (Ideal.Quotient.mk (idealC k) p) =
      Ideal.Quotient.mk (idealC k) (weightedHomogeneousComponent auxiliaryWeight n p) := by
  exact congrArg (Ideal.Quotient.mk (idealC k))
    (MvPolynomial.decompose'_apply k auxiliaryWeight p n)

/-- Fiber projections commute with passage to the quotient. -/
@[simp]
theorem fiber_proj_mk (n : ℤ) (p : P k 5) :
    GradedAlgebra.proj (fiberPiece k) n (Ideal.Quotient.mk (idealC k) p) =
      Ideal.Quotient.mk (idealC k) (weightedHomogeneousComponent fiberWeight n p) := by
  exact congrArg (Ideal.Quotient.mk (idealC k))
    (MvPolynomial.decompose'_apply k fiberWeight p n)

/-- Coefficientwise weighted projections for arbitrary weight vectors commute. -/
theorem weightedHomogeneousComponent_commute (w w' : Fin 5 → ℤ)
    (m n : ℤ) (p : P k 5) :
    weightedHomogeneousComponent w m (weightedHomogeneousComponent w' n p) =
      weightedHomogeneousComponent w' n (weightedHomogeneousComponent w m p) := by
  ext d
  by_cases hm : Finsupp.weight w d = m <;>
    by_cases hn : Finsupp.weight w' d = n <;>
      simp only [coeff_weightedHomogeneousComponent, hm, hn, ↓reduceIte]

/-- The fiber and auxiliary gradings are compatible on the actual quotient:
their homogeneous projection maps commute. -/
theorem auxiliary_fiber_proj_commute (m n : ℤ) (z : C k) :
    GradedAlgebra.proj (auxiliaryPiece k) m (GradedAlgebra.proj (fiberPiece k) n z) =
      GradedAlgebra.proj (fiberPiece k) n (GradedAlgebra.proj (auxiliaryPiece k) m z) := by
  refine Quotient.inductionOn' z ?_
  intro p
  change GradedAlgebra.proj (auxiliaryPiece k) m
      (GradedAlgebra.proj (fiberPiece k) n (Ideal.Quotient.mk (idealC k) p)) =
    GradedAlgebra.proj (fiberPiece k) n
      (GradedAlgebra.proj (auxiliaryPiece k) m (Ideal.Quotient.mk (idealC k) p))
  simp only [auxiliary_proj_mk, fiber_proj_mk]
  exact congrArg (Ideal.Quotient.mk (idealC k))
    (weightedHomogeneousComponent_commute k auxiliaryWeight fiberWeight m n p)

end StableCoordinate.Obstruction

end

end OAI
