import OAI.Geometry.BundleTests.Base
import OAI.Geometry.ComplexBundle.Pullback

namespace OAI

noncomputable section

/-! Test bundles, Hermitian metrics, and their trivial initial stage. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

/-- The zero label denotes L₀; positive labels denote hyperplane pullbacks. -/
def testLineChartIndex (m R : ℕ) : Option (Fin R) → Type
  | none => Unit
  | some i => Fin (testProjectiveDimension m R i + 1)

def testLineCore (m R : ℕ) (i : Option (Fin R)) :
    VectorBundleCore ℂ (BundleTestBase m R) ℂ (testLineChartIndex m R i) :=
  match i with
  | none => trivialLineCore (BundleTestBase m R)
  | some i => pullbackLineCore
      (projectionDualLineCore (testProjectiveDimension m R i+1)) (bundleTestProjection m R i)

/-- The positive-labelled line is topologically the preserved hyperplane
pullback, including its total-space topology. -/
def testLineCoreHyperplaneHomeomorph (m R : ℕ) (i : Fin R) :
    TotalSpace ℂ (testLineCore m R (some i)).Fiber ≃ₜ
      TotalSpace ℂ (TestHyperplaneLine m R i) :=
  pullbackLineCoreTotalHomeomorph _ _

def testSummandLineIndex {R j : ℕ} (hj : j≤R) (i : Fin (j+1)) : Option (Fin R) :=
  if h : i.val=0 then none else some ⟨i.val-1,by omega⟩

@[simp] theorem testSummandLineIndex_zero {R j : ℕ} (hj : j≤R) :
    testSummandLineIndex hj 0 = none := by simp [testSummandLineIndex]

abbrev TestBundleSlot (m R j : ℕ) := Σ i : Fin (j+1), Fin (testMultiplicity m R j i)

def testBundleCore (m R j : ℕ) (hj : j≤R) :=
  finiteLineSumCore (fun s : TestBundleSlot m R j =>
    testLineCore m R (testSummandLineIndex hj s.1))

abbrev TestBundle (m R j : ℕ) (hj : j≤R) := (testBundleCore m R j hj).Fiber

instance (m R j : ℕ) (hj : j≤R) :
    FiberBundle (EuclideanSpace ℂ (TestBundleSlot m R j)) (TestBundle m R j hj) := inferInstance

instance (m R j : ℕ) (hj : j≤R) :
    VectorBundle ℂ (EuclideanSpace ℂ (TestBundleSlot m R j)) (TestBundle m R j hj) := inferInstance

theorem testBundle_finrank (m R j : ℕ) (hj : j≤R) (y : BundleTestBase m R) :
    Module.finrank ℂ (TestBundle m R j hj y) = testRank m R j := by
  change Module.finrank ℂ (EuclideanSpace ℂ (TestBundleSlot m R j)) = _
  simpa [TestBundleSlot] using (sum_testMultiplicity (m := m) hj)

/-- Actual topological component maps, one for every occurrence of each line. -/
theorem continuous_testBundle_component (m R j : ℕ) (hj : j≤R)
    (s : TestBundleSlot m R j) :
    Continuous (finiteLineSumComponent
      (fun s : TestBundleSlot m R j => testLineCore m R (testSummandLineIndex hj s.1)) s) :=
  continuous_finiteLineSumComponent _ _

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky

theorem complex_unit_mul_inner (u : ℂ) (hu : star u*u=1) (z w : ℂ) :
    inner ℂ (u*z) (u*w) = inner ℂ z w := by
  change (u*w)*star (u*z) = w*star z
  rw [star_mul]
  calc
    (u*w) * (star z * star u) = (star u*u)*(w*star z) := by ring
    _ = _ := by rw [hu,one_mul]

theorem testLineCore_unitary (m R : ℕ) (i : Option (Fin R))
    (a b : testLineChartIndex m R i) (y : BundleTestBase m R)
    (ha : y ∈ (testLineCore m R i).baseSet a)
    (hb : y ∈ (testLineCore m R i).baseSet b) (z w : ℂ) :
    inner ℂ ((testLineCore m R i).coordChange a b y z)
      ((testLineCore m R i).coordChange a b y w) = inner ℂ z w := by
  cases i with
  | none => rfl
  | some i =>
    apply complex_unit_mul_inner
    simpa only [star_star,mul_comm] using projectionLineTransition_unitary a b ((bundleTestProjection m R i) y) ha hb

theorem testBundleLineCores_unitary (m R j : ℕ) (hj : j≤R) :
    LineCoreIsUnitary (fun s : TestBundleSlot m R j =>
      testLineCore m R (testSummandLineIndex hj s.1)) :=
  fun _ => testLineCore_unitary m R _

instance testBundleFiberNormedAddCommGroup (m R j : ℕ) (hj : j≤R)
    (y : BundleTestBase m R) : NormedAddCommGroup (TestBundle m R j hj y) :=
  finiteLineSumFiberNormedAddCommGroup _ y

instance testBundleFiberInnerProductSpace (m R j : ℕ) (hj : j≤R)
    (y : BundleTestBase m R) : InnerProductSpace ℂ (TestBundle m R j hj y) :=
  finiteLineSumFiberInnerProductSpace _ y

theorem testBundle_inner_continuousOn (m R j : ℕ) (hj : j≤R)
    (A : Set (BundleTestBase m R)) (v w : ∀ y, TestBundle m R j hj y)
    (hv : ContinuousOn (fun y => TotalSpace.mk' (EuclideanSpace ℂ (TestBundleSlot m R j)) y (v y)) A)
    (hw : ContinuousOn (fun y => TotalSpace.mk' (EuclideanSpace ℂ (TestBundleSlot m R j)) y (w y)) A) :
    ContinuousOn (fun y => inner ℂ (v y) (w y)) A :=
  finiteLineSum_inner_continuousOn _ (testBundleLineCores_unitary m R j hj) A v w hv hw

end Kaplansky

end

open Bundle Topology
namespace Kaplansky

theorem testBundle_zero_baseSet (m R : ℕ)
    (a : ∀ s : TestBundleSlot m R 0, testLineChartIndex m R (testSummandLineIndex (Nat.zero_le R) s.1)) :
    (testBundleCore m R 0 (Nat.zero_le R)).baseSet a = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    change ∀ s : TestBundleSlot m R 0,
      y ∈ (testLineCore m R (testSummandLineIndex (Nat.zero_le R) s.1)).baseSet (a s)
    rintro ⟨i,b⟩
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact Set.mem_univ _

/-- A global linear bundle chart for E₀. This proves topological triviality,
not just that its fibers have the desired dimension. -/
def testBundleZeroTotalHomeomorph (m R : ℕ) :
    TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R 0)) (TestBundle m R 0 (Nat.zero_le R)) ≃ₜ
      BundleTestBase m R × EuclideanSpace ℂ (TestBundleSlot m R 0) := by
  let C := testBundleCore m R 0 (Nat.zero_le R)
  let a := C.indexAt (bundleTestBasePoint m R)
  have hb : (C.localTriv a).baseSet = Set.univ := testBundle_zero_baseSet m R a
  exact (C.localTriv a).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (by rw [(C.localTriv a).source_eq,hb]; simp)
    (by rw [(C.localTriv a).target_eq,hb]; simp)

@[simp] theorem testBundleZeroTotalHomeomorph_apply (m R : ℕ)
    (z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R 0)) (TestBundle m R 0 (Nat.zero_le R))) :
    testBundleZeroTotalHomeomorph m R z =
      (z.proj,(show EuclideanSpace ℂ (TestBundleSlot m R 0) from z.2)) := by
  apply Prod.ext
  · rfl
  · ext ⟨i,b⟩
    have hi : i=0 := Fin.eq_zero i
    subst i
    rfl

end Kaplansky

end

end OAI
