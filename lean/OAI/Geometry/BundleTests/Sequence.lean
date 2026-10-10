import OAI.Geometry.BundleTests.Normalized
import OAI.Geometry.ComplexBundle.LineStage

namespace OAI

noncomputable section

/-! Prefix and full test steps, pullbacks, and the infinite test sequence. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann

/-- Pull continuous normalized maps from a projective subproduct to the
full product. Continuity uses the actual line-sum pullback topology. -/
def lineSumPullbackStep {ι κ S T : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Fintype T]
    (K : κ → ℕ) (f : ι → κ) (a : S → Option ι) (b : T → Option ι)
    (X : ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ T)
      (SmoothLineSumBundle (fun i => K (f i)) a) (SmoothLineSumBundle (fun i => K (f i)) b)) :
    ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ T)
      (SmoothLineSumBundle K (fun s => (a s).map f))
      (SmoothLineSumBundle K (fun t => (b t).map f)) where
  tuple x := X.tuple (projectiveRestrict K f x)
  continuous_forward i := by
    let g := fun z : TotalSpace (EuclideanSpace ℂ S)
      (SmoothLineSumBundle K (fun s => (a s).map f)) => z.proj
    have hg : Continuous g := FiberBundle.continuous_proj _ _
    have hin := (continuous_lineSum_restrict_iff K f a g (fun z => z.2) hg).mp continuous_id
    exact (continuous_lineSum_restrict_iff K f b g
      (fun z => (X.tuple (projectiveRestrict K f z.proj)).forward i z.2) hg).mpr
      ((X.continuous_forward i).comp hin)
  continuous_reverse i := by
    let g := fun z : TotalSpace (EuclideanSpace ℂ T)
      (SmoothLineSumBundle K (fun t => (b t).map f)) => z.proj
    have hg : Continuous g := FiberBundle.continuous_proj _ _
    have hin := (continuous_lineSum_restrict_iff K f b g (fun z => z.2) hg).mp continuous_id
    exact (continuous_lineSum_restrict_iff K f a g
      (fun z => (X.tuple (projectiveRestrict K f z.proj)).reverse i z.2) hg).mpr
      ((X.continuous_reverse i).comp hin)

attribute [local irreducible] bundleAdjoint finiteCoordinateEquiv

/-- The previously constructed normalized tuple, including both directions
of continuity and the actual adjoint identity. -/
theorem testCoordinateStep_nonempty {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    Nonempty (TestCoordinateStepType m R j hj) := by
  obtain ⟨X,hX,hA,hN⟩ := exists_test_normalized_maps hm hj
  refine ⟨{
    tuple := fun y =>
      { forward := X y
        reverse := bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y
        adjoint_inner := bundleAdjoint_inner (d := testRank m R j) (r := testRank m R (j+1)) X y
        column := (hN y).1
        row := (hN y).2 }
    continuous_forward := hX
    continuous_reverse := hA }⟩

def testCoordinateStep {m R j : ℕ} (hm : 0<m) (hj : j<R) : TestCoordinateStepType m R j hj :=
  Classical.choice (testCoordinateStep_nonempty hm hj)

def testPrefixStep {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ContinuousNormalizedStep (EuclideanSpace ℂ (TestBundleSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j))
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1))) :=
  (testCoordinateStep hm hj).congr
    (finiteCoordinateUnitary _ _ _ (testBundleSlot_card (Nat.le_of_lt hj))).symm
    ((finiteCoordinateUnitary _ _ _ (testNextSlot_card hj)).symm.trans (testNextStageUnitary m R j hj))

end

open ComplexGrassmann

theorem testSummandLineIndex_map {n b R : ℕ} (hn : n≤b) (hb : b≤R) (s : Fin (n+1)) :
    (testSummandLineIndex hn s).map (fun i => i.castLE hb) = testSummandLineIndex (hn.trans hb) s := by
  unfold testSummandLineIndex
  split <;> simp_all

/-- A single coherent presentation of the finite stages on full Y. -/
abbrev FullTestBundle (m R j : ℕ) (hj : j≤R) :=
  SmoothTestBundle m R R j (Nat.le_refl R) hj

def testFullStep {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ContinuousNormalizedStep (EuclideanSpace ℂ (TestBundleSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (FullTestBundle m R j (Nat.le_of_lt hj)) (FullTestBundle m R (j+1) hj) := by
  let X := lineSumPullbackStep (testProjectiveDimension m R) (fun i : Fin (j+1) => i.castLE hj)
    (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
    (fun s : TestBundleSlot m R (j+1) => testSummandLineIndex (Nat.le_refl (j+1)) s.1)
    (testPrefixStep hm hj)
  have ha : (fun s : TestBundleSlot m R j =>
      (testSummandLineIndex (Nat.le_succ j) s.1).map (fun i => i.castLE hj)) =
      fun s => testSummandLineIndex (Nat.le_of_lt hj) s.1 :=
    funext (fun s => testSummandLineIndex_map (Nat.le_succ j) hj s.1)
  have hb : (fun s : TestBundleSlot m R (j+1) =>
      (testSummandLineIndex (Nat.le_refl (j+1)) s.1).map (fun i => i.castLE hj)) =
      fun s => testSummandLineIndex hj s.1 :=
    funext (fun s => testSummandLineIndex_map (Nat.le_refl (j+1)) hj s.1)
  rw [ha,hb] at X
  exact X

def testLineStage (m R j : ℕ) (hj : j≤R) : LineStage (testProjectiveDimension m R) :=
  ⟨TestBundleSlot m R j,inferInstance,fun s => testSummandLineIndex hj s.1⟩

def testSequenceStage (m R : ℕ) (j : ℕ) : LineStage (testProjectiveDimension m R) :=
  if h : j≤R then testLineStage m R j h
  else (testLineStage m R R (Nat.le_refl R)).tail (j-R)

theorem testSequenceStage_prefix {m R j : ℕ} (hj : j≤R) :
    testSequenceStage m R j = testLineStage m R j hj := by simp [testSequenceStage,hj]

theorem testSequenceStage_tail {m R j : ℕ} (hj : R≤j) :
    testSequenceStage m R j = (testLineStage m R R (Nat.le_refl R)).tail (j-R) := by
  by_cases h : j≤R
  · have he : j=R := Nat.le_antisymm h hj
    subst j
    simp [testSequenceStage,LineStage.tail]
  · simp [testSequenceStage,h]

/-- All 24 normalized bundle maps for all levels, constructed solely from
m>0. Both forward maps and their genuine adjoints are continuous over the
single full projective product Y. -/
def testSequenceStep {m R : ℕ} (hm : 0<m) (j : ℕ) :
    (testSequenceStage m R j).Step (testSequenceStage m R (j+1)) := by
  by_cases hj : j<R
  · rw [testSequenceStage_prefix (Nat.le_of_lt hj),testSequenceStage_prefix hj]
    exact testFullStep hm hj
  · have hR : R≤j := Nat.le_of_not_gt hj
    rw [testSequenceStage_tail hR,testSequenceStage_tail (hR.trans (Nat.le_succ j))]
    have hs : j+1-R=(j-R)+1 := by omega
    rw [hs]
    exact (testLineStage m R R (Nat.le_refl R)).tailStep (j-R)

theorem testSequenceStage_rank {m R j : ℕ} (hj : j≤R)
    (y : SmoothTestBase m R) :
    Module.finrank ℂ ((testSequenceStage m R j).Fiber y) = testRank m R j := by
  rw [testSequenceStage_prefix hj]
  exact smoothTestBundle_finrank m R R j (Nat.le_refl R) hj y

theorem testSequenceStage_tail_rank {m R j : ℕ} (hj : R≤j)
    (y : SmoothTestBase m R) :
    Module.finrank ℂ ((testSequenceStage m R j).Fiber y) = 2^(j-R)*testRank m R R := by
  rw [testSequenceStage_tail hj]
  change Module.finrank ℂ (EuclideanSpace ℂ ((testLineStage m R R (Nat.le_refl R)).tail (j-R)).Slot)=_
  rw [finrank_euclideanSpace,LineStage.tail_card]
  exact congrArg (fun n => 2^(j-R)*n) (testBundleSlot_card (Nat.le_refl R))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

theorem smoothTestBundle_zero_baseSet (m R : ℕ)
    (a : ∀ s : TestBundleSlot m R 0,
      productLineChartIndex (testProjectiveDimension m R) (testSummandLineIndex (Nat.zero_le R) s.1)) :
    (smoothTestBundleCore m R R 0 (Nat.le_refl R) (Nat.zero_le R)).baseSet a = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    change ∀ s : TestBundleSlot m R 0,
      y ∈ (productLineCore (testProjectiveDimension m R) (testSummandLineIndex (Nat.zero_le R) s.1)).baseSet (a s)
    rintro ⟨i,b⟩
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact Set.mem_univ _

/-- A global linear chart for the actual full-product E₀, identifying it
with Y times its Hilbert fiber, with exactly d₀ coordinates. -/
def smoothTestBundleZeroTotalHomeomorph (m R : ℕ) :
    TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R 0)) (FullTestBundle m R 0 (Nat.zero_le R)) ≃ₜ
      SmoothTestBase m R × EuclideanSpace ℂ (TestBundleSlot m R 0) := by
  let C := smoothTestBundleCore m R R 0 (Nat.le_refl R) (Nat.zero_le R)
  let a := C.indexAt (testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R))
  have hb : (C.localTriv a).baseSet = Set.univ := smoothTestBundle_zero_baseSet m R a
  exact (C.localTriv a).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (by rw [(C.localTriv a).source_eq,hb]; simp)
    (by rw [(C.localTriv a).target_eq,hb]; simp)

@[simp] theorem smoothTestBundleZeroTotalHomeomorph_apply (m R : ℕ)
    (z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R 0)) (FullTestBundle m R 0 (Nat.zero_le R))) :
    smoothTestBundleZeroTotalHomeomorph m R z =
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
