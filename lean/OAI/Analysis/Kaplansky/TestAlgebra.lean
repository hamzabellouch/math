import OAI.Analysis.Kaplansky.BundleWords
import OAI.Analysis.Kaplansky.Polynomials
import OAI.Analysis.Kaplansky.ShiftAlgebra
import OAI.Geometry.BundleTests.Sequence
import Mathlib.Data.PNat.Basic

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

abbrev ActualTestIndex := Σ m : ℕ+, Σ R : ℕ+, SmoothTestBase m.val R.val

instance : Nonempty ActualTestIndex :=
  ⟨⟨1,1,testBaseProjectiveHomeomorph 1 1 (bundleTestBasePoint 1 1)⟩⟩

abbrev ActualTestFiber (z : ActualTestIndex) (j : ℕ) :=
  EuclideanSpace ℂ (testSequenceStage z.1.val z.2.1.val j).Slot

instance actualTestFiber_zero_nontrivial (z : ActualTestIndex) : Nontrivial (ActualTestFiber z 0) := by
  change Nontrivial (EuclideanSpace ℂ (testSequenceStage z.1.val z.2.1.val 0).Slot)
  rw [testSequenceStage_prefix (Nat.zero_le _)]
  let : Nonempty (TestBundleSlot z.1.val z.2.1.val 0) := ⟨⟨0,⟨0,by
    change 0 < 64*z.1.val*4^(z.2.1.val-0)
    positivity⟩⟩⟩
  exact inferInstanceAs (Nontrivial (EuclideanSpace ℂ (TestBundleSlot z.1.val z.2.1.val 0)))

/-- Actual bounded blocks of the normalized bundle test, at all levels. -/
def actualTestOperator (i : Fin 24) (z : ActualTestIndex) (j : ℕ) :
    ActualTestFiber z j →L[ℂ] ActualTestFiber z (j+1) := by
  let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
    (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
  exact T.operator i

theorem actualTestOperator_column (z : ActualTestIndex) (j : ℕ) :
    ∑ i, (actualTestOperator i z j).adjoint.comp (actualTestOperator i z j) =
      ContinuousLinearMap.id ℂ (ActualTestFiber z j) :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_column
    exact h

theorem actualTestOperator_row (z : ActualTestIndex) (j : ℕ) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1)) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_row
    exact h

theorem actualTestOperator_norm (i : Fin 24) (z : ActualTestIndex) (j : ℕ) :
    ‖actualTestOperator i z j‖ ≤ 1 :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_norm_le i
    exact h

open scoped BigOperators

def actualTestWord {m R : ℕ} (hm : 0<m) (w : List (Bool × Fin 24)) :
    BundleWordValue (testSequenceStage m R) := bundleWordValue (testSequenceStep (R := R) hm) w

theorem actualTestWord_level_le {m R : ℕ} (hm : 0<m) (w : List (Bool × Fin 24)) :
    (actualTestWord (R := R) hm w).level ≤ w.length := bundleWordValue_level_le _ w

theorem actualTestWord_continuous {m R : ℕ} (hm : 0<m) (w : List (Bool × Fin 24)) :
    Continuous (fun z : TotalSpace (testSequenceStage m R 0).Model (testSequenceStage m R 0).Fiber =>
      TotalSpace.mk' (testSequenceStage m R (actualTestWord (R := R) hm w).level).Model z.proj
        ((actualTestWord (R := R) hm w).map z.proj z.2)) :=
  (actualTestWord (R := R) hm w).continuous_map

/-- Exact agreement with the actual operators used in the constructed
bounded-product algebra; this includes constants and every adjoint case. -/
theorem actualTestWord_shift_eval (z : ActualTestIndex) (w : List (Bool × Fin 24))
    (v : ActualTestFiber z 0) :
    applyWord (shiftLetter (fun i j => actualTestOperator i z j)
      (fun i j => actualTestOperator_norm i z j)) w (lp.single 2 0 v) =
      lp.single 2 (actualTestWord (R := z.2.1.val) z.1.property w).level
        ((actualTestWord (R := z.2.1.val) z.1.property w).map z.2.2 v) :=
  bundleWordValue_shift_eval (testSequenceStep (R := z.2.1.val) z.1.property) w z.2.2 v

/-- The finite degree restriction for all actual test coordinates. -/
theorem actualTestPolynomial_from_bottom (z : ActualTestIndex) {J : Type*}
    (s : Finset J) (w : J → List (Bool × Fin 24)) (c : J → ℂ)
    (hdeg : ∀ j ∈ s, (w j).length ≤ z.2.1.val) (v : ActualTestFiber z 0) :
    (∑ j ∈ s, c j • applyWord (shiftLetter (fun i k => actualTestOperator i z k)
      (fun i k => actualTestOperator_norm i z k)) (w j) (lp.single 2 0 v)) ∈
      hilbertLevels z.2.1.val :=
  shift_polynomial_from_bottom (fun i k => actualTestOperator i z k)
    (fun i k => actualTestOperator_norm i z k) s w c z.2.1.val hdeg v

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

instance actualHilbert_nontrivial (z : ActualTestIndex) : Nontrivial (FiberHilbertSum (ActualTestFiber z)) :=
  fiberHilbertSum_nontrivial

abbrev ActualHilbert (z : ActualTestIndex) := FiberHilbertSum (ActualTestFiber z)

def actualBoundedGenerator (i : Fin 24) : BoundedProduct (fun z : ActualTestIndex => ActualHilbert z →L[ℂ] ActualHilbert z) :=
  boundedProductLift (fun z => forwardShift (actualTestOperator i z) (actualTestOperator_norm i z))
    (fun z => forwardShift_norm_le (actualTestOperator i z) (actualTestOperator_norm i z))

abbrev ActualAlgebra := generatedAlgebra (Set.range actualBoundedGenerator)

theorem actual_test_shift_algebra :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra ∧
      (∑ i, star (generatedGenerator actualBoundedGenerator i) *
        generatedGenerator actualBoundedGenerator i = 1) ∧
      (∑ i, generatedGenerator actualBoundedGenerator i *
        star (generatedGenerator actualBoundedGenerator i) ≤ (2/3 : ℂ) • 1) := by
  have hrow : ∀ z j, ((((2/3 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1))) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive := by
    intro z j
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using actualTestOperator_row z j
  have h := source_shift_algebra actualTestOperator actualTestOperator_column (2/3)
    (by norm_num) hrow
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  exact h


def actualRepresentation (z : ActualTestIndex) : ActualAlgebra →⋆ₐ[ℂ] (ActualHilbert z →L[ℂ] ActualHilbert z) where
  toFun b := b.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem actualRepresentation_generator (z : ActualTestIndex) (i : Fin 24) :
    actualRepresentation z (generatedGenerator actualBoundedGenerator i) =
      forwardShift (actualTestOperator i z) (actualTestOperator_norm i z) := rfl

theorem actualRepresentation_norm (z : ActualTestIndex) (b : ActualAlgebra) :
    ‖actualRepresentation z b‖ ≤ ‖b‖ := by
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero b.val z

abbrev actualAlgebra_cstar : CStarAlgebra ActualAlgebra := inferInstance

theorem actualAlgebra_nontrivial_separable :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra := by
  have h := actual_test_shift_algebra
  exact ⟨h.1,h.2.1⟩

end Kaplansky

end

end OAI
