import OAI.Geometry.BundleTests.Assembly
import OAI.Geometry.ComplexBundle.Maps
import OAI.Geometry.ComplexBundle.Tuples

namespace OAI

noncomputable section

/-! Normalized test maps, slot regrouping, and unitary coordinate changes. -/

section
open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

abbrev TestNextCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (testNextLabel m R j) (testRank m R (j+1)) (testNextSlot_card hj)

/-- The actual 24-map expansion transported into the same concrete
Hermitian coordinate bundles used by ordinary bundle normalization. -/
theorem exists_test_coordinate_expanding_maps {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ T : ∀ y, Fin 24 → TestSourceCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y,
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R (j+1)) → ℂ) z.proj (T z.proj i z.2))) ∧
      ∀ y, IntrinsicExpanding (T y) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_twentyFour_expanding_maps hm hj
  let e := finiteCoordinateEquiv (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj) (m := m))
  let f := finiteCoordinateEquiv (testRank m R (j+1)) (testNextSlot_card hj (m := m))
  let a := fun y => (show SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y ≃ₗ[ℂ]
    TestSourceCoordinates m R j hj y from e.toLinearEquiv)
  let b := fun y => (show (smoothNextCore m R j hj).Fiber y ≃ₗ[ℂ]
    TestNextCoordinates m R j hj y from f.toLinearEquiv)
  refine ⟨fun y i => (b y).toLinearMap.comp ((T y i).comp (a y).symm.toLinearMap),?_,?_⟩
  · intro i
    let H := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
      (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))
    let G := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (testNextLabel m R j) (testRank m R (j+1)) (testNextSlot_card hj)
    exact G.continuous.comp ((hT i).comp H.symm.continuous)
  · intro y
    exact intrinsicExpanding_equiv (T y) (a y) (b y) (hExp y)

theorem exists_test_normalized_maps {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ X : ∀ y, Fin 24 → TestSourceCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y,
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R (j+1)) → ℂ) z.proj (X z.proj i z.2))) ∧
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R (j+1)) → ℂ) (TestNextCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R j) → ℂ) z.proj
          (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X z.proj i z.2))) ∧
      ∀ y, (∑ i, (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y i).comp (X y i)) = LinearMap.id ∧
        ∀ v : TestNextCoordinates m R j hj y, 0 ≤ inner ℂ v
          (((2/3 : ℂ) • (LinearMap.id : TestNextCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y) -
            ∑ i, (X y i).comp (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y i)) v) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_coordinate_expanding_maps hm hj
  exact exists_continuous_normalized_bundle_maps
    (finiteCoordinate_continuousHermitianMetric _ _ _ _)
    (finiteCoordinate_continuousHermitianMetric _ _ _ _) T hT hExp

end Kaplansky

end

section
open Bundle
namespace Kaplansky
open ComplexGrassmann

def testNextSlotEquiv (m R j : ℕ) : TestNextSlot m R j ≃ TestBundleSlot m R (j+1) where
  toFun := Sum.elim (fun s => ⟨s.1.castSucc,s.2⟩) (fun k => ⟨Fin.last (j+1),k⟩)
  invFun s := Fin.lastCases (fun k => Sum.inr k) (fun i k => Sum.inl ⟨i,k⟩) s.1 s.2
  left_inv s := by cases s <;> simp
  right_inv s := by
    obtain ⟨i,k⟩ := s
    induction i using Fin.lastCases <;> simp

theorem testNextLabel_eq (m R j : ℕ) (s : TestNextSlot m R j) :
    testNextLabel m R j s = testSummandLineIndex (Nat.le_refl (j+1)) (testNextSlotEquiv m R j s).1 := by
  cases s with
  | inl s =>
    obtain ⟨i,k⟩ := s
    simp only [testNextLabel,Sum.elim_inl,testNextSlotEquiv,Equiv.coe_fn_mk]
    simp [testSummandLineIndex]
  | inr k =>
    simp only [testNextLabel,Sum.elim_inr,testNextSlotEquiv,Equiv.coe_fn_mk]
    simp [testSummandLineIndex]
    rfl

/-- The regrouped target and E_{j+1} are isomorphic as actual topological
bundles, not merely vector spaces of the same rank. -/
def testNextStageTotalHomeomorph (m R j : ℕ) (hj : j<R) :
    TotalSpace (EuclideanSpace ℂ (TestNextSlot m R j)) (smoothNextCore m R j hj).Fiber ≃ₜ
      TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
        (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1))) := by
  let K := stageProjectiveDimensions m R (j+1) hj
  let e := testNextSlotEquiv m R j
  let P : (TestNextSlot m R j → Option (Fin (j+1))) → Type := fun label =>
    TotalSpace (EuclideanSpace ℂ (TestNextSlot m R j)) (SmoothLineSumBundle K label) ≃ₜ
      TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
        (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1)))
  have he : testNextLabel m R j = fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1 :=
    funext (testNextLabel_eq m R j)
  have h : P (fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1) :=
    lineSumReindexTotalHomeomorph
      (fun s : TestBundleSlot m R (j+1) => productLineCore K (testSummandLineIndex (Nat.le_refl (j+1)) s.1)) e
  exact Eq.mp (congrArg P he.symm) h

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

/-- The finite-coordinate change preserves the actual Hermitian metric and
the actual total-space topology simultaneously. -/
def finiteCoordinateUnitary {S ι : Type*} [Fintype S] [Fintype ι]
    (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d) :
    UnitaryBundleEquiv (EuclideanSpace ℂ S) (Fin d → ℂ)
      (SmoothLineSumBundle K label) (FiniteCoordinateBundle K label d hd) where
  fiber x :=
    { toLinearEquiv := (finiteCoordinateEquiv d hd).toLinearEquiv
      norm_map' := fun v => by
        change ‖(finiteCoordinateEquiv d hd).symm (finiteCoordinateEquiv d hd v)‖ = ‖v‖
        exact congrArg norm ((finiteCoordinateEquiv d hd).symm_apply_apply
          (show EuclideanSpace ℂ S from v)) }
  continuous_forward := (finiteCoordinateTotalHomeomorph K label d hd).continuous
  continuous_reverse := (finiteCoordinateTotalHomeomorph K label d hd).symm.continuous

/-- Reindexing an orthogonal line sum is unitary on fibers and continuous
in both directions on the actual total space. -/
def lineSumReindexUnitary {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
    {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (e : T ≃ S) :
    UnitaryBundleEquiv (EuclideanSpace ℂ T) (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun t => C (e t))).Fiber (finiteLineSumCore C).Fiber where
  fiber x :=
    { toLinearEquiv := lineSumReindex C e x
      norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (lineSumReindex_inner C e x) }
  continuous_forward := (lineSumReindexTotalHomeomorph C e).continuous
  continuous_reverse := (lineSumReindexTotalHomeomorph C e).symm.continuous

instance smoothNext_norm (m R j : ℕ) (hj : j<R)
    (x : ProjectiveProduct (stageProjectiveDimensions m R (j+1) hj)) :
    NormedAddCommGroup ((smoothNextCore m R j hj).Fiber x) := smoothLineSum_norm _ _ x

instance smoothNext_inner (m R j : ℕ) (hj : j<R)
    (x : ProjectiveProduct (stageProjectiveDimensions m R (j+1) hj)) :
    InnerProductSpace ℂ ((smoothNextCore m R j hj).Fiber x) := smoothLineSum_inner _ _ x

/-- The replacement-plus-fresh target is the standard next stage as an
ordinary Hermitian bundle, so normalization survives this regrouping. -/
def testNextStageUnitary (m R j : ℕ) (hj : j<R) :
    UnitaryBundleEquiv (EuclideanSpace ℂ (TestNextSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (smoothNextCore m R j hj).Fiber
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1))) := by
  let K := stageProjectiveDimensions m R (j+1) hj
  let e := testNextSlotEquiv m R j
  let P : (TestNextSlot m R j → Option (Fin (j+1))) → Type := fun label =>
    UnitaryBundleEquiv (EuclideanSpace ℂ (TestNextSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (SmoothLineSumBundle K label)
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1)))
  have he : testNextLabel m R j = fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1 :=
    funext (testNextLabel_eq m R j)
  have h : P (fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1) :=
    lineSumReindexUnitary
      (fun s : TestBundleSlot m R (j+1) => productLineCore K (testSummandLineIndex (Nat.le_refl (j+1)) s.1)) e
  exact Eq.mp (congrArg P he.symm) h

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

local instance (priority := 2100) coordinateSourceNorm (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : NormedAddCommGroup (TestSourceCoordinates m R j hj y) :=
  finiteCoordinateHilbertNorm _ _ _ _ y
local instance (priority := 2100) coordinateSourceInner (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : InnerProductSpace ℂ (TestSourceCoordinates m R j hj y) :=
  finiteCoordinateHilbertInner _ _ _ _ y
local instance (priority := 2100) coordinateNextNorm (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : NormedAddCommGroup (TestNextCoordinates m R j hj y) :=
  finiteCoordinateHilbertNorm _ _ _ _ y
local instance (priority := 2100) coordinateNextInner (m R j : ℕ) (hj : j<R)
    (y : SmoothPrefixBase m R j hj) : InnerProductSpace ℂ (TestNextCoordinates m R j hj y) :=
  finiteCoordinateHilbertInner _ _ _ _ y

def TestCoordinateStepType (m R j : ℕ) (hj : j<R) : Type :=
    @ContinuousNormalizedStep (SmoothPrefixBase m R j hj)
      (Fin (testRank m R j) → ℂ) (Fin (testRank m R (j+1)) → ℂ)
      (TestSourceCoordinates m R j hj) (TestNextCoordinates m R j hj)
      (coordinateSourceNorm m R j hj) (coordinateSourceInner m R j hj)
      (coordinateNextNorm m R j hj) (coordinateNextInner m R j hj)
      inferInstance inferInstance

end Kaplansky

end

end OAI
