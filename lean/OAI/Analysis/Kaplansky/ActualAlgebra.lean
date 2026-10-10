import OAI.Analysis.Cuntz.State
import OAI.Analysis.Quasitrace.Defect
import OAI.Geometry.BundleTests.Obstruction

namespace OAI

noncomputable section

/-! The actual M48 algebra, its fixed defect pair, and its Cuntz dimension state. -/

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

private theorem partialSum_leftSquare_fin {B : Type*} [CStarAlgebra B] {N : ℕ}
    (g : Fin N → B) :
    partialSum (leftSquare (fun i => if hi : i < N then g ⟨i, hi⟩ else 0)) N =
      ∑ i : Fin N, star (g i) * g i := by
  simp [partialSum, ← Fin.sum_univ_eq_sum_range, leftSquare]

private theorem partialSum_rightSquare_fin {B : Type*} [CStarAlgebra B] {N : ℕ}
    (g : Fin N → B) :
    partialSum (rightSquare (fun i => if hi : i < N then g ⟨i, hi⟩ else 0)) N =
      ∑ i : Fin N, g i * star (g i) := by
  simp [partialSum, ← Fin.sum_univ_eq_sum_range, rightSquare]

local instance (priority := 3100) actualAlgebraMonoid : Monoid ActualAlgebra :=
  actualAlgebra_cstar.toMonoid
local instance (priority := 3100) actualAlgebraSemiring : Semiring ActualAlgebra :=
  actualAlgebra_cstar.toSemiring

local instance (priority := 3000) actualAlgebraSpectralOrder : PartialOrder ActualAlgebra :=
  CStarAlgebra.spectralOrder ActualAlgebra
local instance (priority := 3000) actualAlgebraSpectralLE : LE ActualAlgebra :=
  (CStarAlgebra.spectralOrder ActualAlgebra).toLE
local instance (priority := 3000) actualAlgebraSpectralOrderedRing : StarOrderedRing ActualAlgebra :=
  CStarAlgebra.spectralOrderedRing ActualAlgebra

abbrev ActualDefectIndex := Fin 24 ⊕ Fin 24
abbrev ActualDefectAlgebra := CStarMatrix ActualDefectIndex ActualDefectIndex ActualAlgebra

instance (priority := 2400) actualDefectAlgebra_cstar : CStarAlgebra ActualDefectAlgebra :=
  CStarMatrix.instCStarAlgebra

local instance (priority := 3100) actualDefectAlgebraSemiring : Semiring ActualDefectAlgebra :=
  actualDefectAlgebra_cstar.toSemiring
local instance (priority := 3100) actualDefectMatrixSemiring (m : ℕ) :
    Semiring (CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra) := CStarMatrix.instSemiring

def actualGeneratorNat (i : ℕ) : ActualAlgebra :=
  if hi : i < 24 then generatedGenerator actualBoundedGenerator ⟨i,hi⟩ else 0

theorem actualGeneratorNat_column : partialSum (leftSquare actualGeneratorNat) 24 = 1 :=
  (partialSum_leftSquare_fin (generatedGenerator actualBoundedGenerator)).trans
    actual_test_shift_algebra.2.2.1

theorem actualGeneratorNat_row :
    partialSum (rightSquare actualGeneratorNat) 24 ≤ ((2/3 : ℝ) : ℂ) • (1 : ActualAlgebra) := by
  have hs := partialSum_rightSquare_fin (generatedGenerator actualBoundedGenerator)
  have hr := actual_test_shift_algebra.2.2.2
  apply (congrArg (fun x : ActualAlgebra =>
    x ≤ ((2/3 : ℝ) : ℂ) • (1 : ActualAlgebra)) hs).mpr
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hr

def actualDefectA : ActualDefectAlgebra := defectA actualGeneratorNat 24
def actualDefectB : ActualDefectAlgebra := defectB actualGeneratorNat 24

/-- The fixed pair in the actual 48-by-48 amplification satisfies the
universal defect bound, without assuming that any quasitrace exists. -/
theorem actualDefectPair_spec :
    PositiveContraction actualDefectA ∧ PositiveContraction actualDefectB ∧
      ∀ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized →
        (1 : ℝ)/144 ≤ (τ (actualDefectA+actualDefectB) - τ actualDefectA - τ actualDefectB).re :=
  uniform_defect_twentyFour actualGeneratorNat actualGeneratorNat_column actualGeneratorNat_row

theorem actualDefectAlgebra_separable : TopologicalSpace.SeparableSpace ActualDefectAlgebra := by
  let := actualAlgebra_nontrivial_separable.2
  exact inferInstanceAs (TopologicalSpace.SeparableSpace
    (ActualDefectIndex → ActualDefectIndex → ActualAlgebra))

/-- Explicit matrix correspondence for every further amplification. -/
def actualDefectAmplificationEquiv (m : ℕ) :
    CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (48*m)) (Fin (48*m)) ActualAlgebra :=
  (cstarMatrixFlatten ActualAlgebra (Fin m) ActualDefectIndex).trans
    (CStarMatrix.reindexₐ ℂ ActualAlgebra
      ((Fintype.equivFin (Fin m × ActualDefectIndex)).trans
        (finCongr (by simp [ActualDefectIndex,Nat.mul_comm]))))

theorem actualDefectAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra) := by
  intro hp
  exact actualAlgebra_matrix_not_properlyInfinite (m := 48*m) (by omega)
    (properlyInfinite_map (actualDefectAmplificationEquiv m).toStarAlgHom hp)

theorem mainTarget_of_actualDefectQuasitrace
    (hq : ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo) : MainTarget := by
  refine ⟨ActualDefectAlgebra,inferInstance,actualDefectAlgebra_separable,hq,
    actualDefectA,actualDefectB,actualDefectPair_spec.1,actualDefectPair_spec.2.1,?_⟩
  intro τ hτ _
  exact actualDefectPair_spec.2.2 τ hτ

end

/-- An actual normalized dimension state exists for the constructed algebra.
No quasitrace-existence premise, simplicity, or exactness assumption is used. -/
theorem actualCuntzDimensionState_nonempty : Nonempty (CuntzDimensionState ActualDefectAlgebra) :=
  cuntzDimensionState_nonempty fun _ hk => actualDefectAlgebra_matrix_not_properlyInfinite hk

/-- A chosen state on actual Cuntz classes. No analytic correspondence is claimed. -/
def actualCuntzDimensionState : CuntzDimensionState ActualDefectAlgebra :=
  Classical.choice actualCuntzDimensionState_nonempty

theorem actualCuntzDimensionState_unit (n : ℕ) :
    actualCuntzDimensionState.value (.unit n) = (n : ℝ) :=
  actualCuntzDimensionState.value_unit n

end Kaplansky

end

end OAI
