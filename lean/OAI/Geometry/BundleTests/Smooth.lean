import OAI.Geometry.ComplexBundle.Replacement
import OAI.Geometry.ComplexBundle.SmoothLine

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Topology
open scoped Manifold ContDiff BigOperators
namespace Kaplansky
open ComplexGrassmann

abbrev SmoothTestBase (m R : ℕ) := ProjectiveProduct (testProjectiveDimension m R)
abbrev SmoothTestModel (m R : ℕ) := ProjectiveProductModel (testProjectiveDimension m R)

def testFactorProjectiveHomeomorph (m R : ℕ) (i : Fin R) :
    projectionSpace (testProjectiveDimension m R i+1) 1 ≃ₜ
      Grassmann 1 (testProjectiveDimension m R i) := by
  let P : ℕ → Type := fun d => projectionSpace d 1 ≃ₜ Grassmann 1 (testProjectiveDimension m R i)
  exact Eq.mp (congrArg P (Nat.add_comm 1 (testProjectiveDimension m R i)))
    (projectiveProjectionHomeomorph (testProjectiveDimension m R i))

def testBaseProjectiveHomeomorph (m R : ℕ) : BundleTestBase m R ≃ₜ SmoothTestBase m R :=
  Homeomorph.piCongrRight (testFactorProjectiveHomeomorph m R)

instance (m R : ℕ) : IsManifold 𝓘(ℝ,SmoothTestModel m R) ∞ (SmoothTestBase m R) := inferInstance
instance (m R : ℕ) : CompactSpace (SmoothTestBase m R) := inferInstance
instance (m R : ℕ) : T2Space (SmoothTestBase m R) := inferInstance

abbrev SmoothPrefixBase (m R j : ℕ) (hj : j<R) :=
  ProjectiveProduct (fun i : Fin (j+1) => testProjectiveDimension m R (i.castLE hj))
abbrev SmoothPrefixModel (m R j : ℕ) (hj : j<R) :=
  ProjectiveProductModel (fun i : Fin (j+1) => testProjectiveDimension m R (i.castLE hj))

theorem smoothPrefix_incidence_margin {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    3*Module.finrank ℝ (SmoothPrefixModel m R j hj) < 40*m*testRank m R j := by
  rw [projectiveProduct_real_finrank]
  have h := testPrefixDimension_margin hm hj
  change 3*testPrefixDimension m R j hj < _ at h
  change 3*(2*testPrefixDimension m R j hj)<_
  nlinarith

end Kaplansky

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

abbrev stageProjectiveDimensions (m R b : ℕ) (hb : b≤R) : Fin b → ℕ :=
  fun i => testProjectiveDimension m R (i.castLE hb)

/-- E_n on the first b projective factors, retaining the full-R K_i. -/
def smoothTestBundleCore (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :=
  smoothLineSumCore (stageProjectiveDimensions m R b hb)
    (fun s : TestBundleSlot m R n => testSummandLineIndex hn s.1)

abbrev SmoothTestBundle (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :=
  (smoothTestBundleCore m R b n hb hn).Fiber

instance smoothTestBundle_norm (m R b n : ℕ) (hb : b≤R) (hn : n≤b)
    (P : ProjectiveProduct (stageProjectiveDimensions m R b hb)) :
    NormedAddCommGroup (SmoothTestBundle m R b n hb hn P) := smoothLineSum_norm _ _ P
instance smoothTestBundle_inner (m R b n : ℕ) (hb : b≤R) (hn : n≤b)
    (P : ProjectiveProduct (stageProjectiveDimensions m R b hb)) :
    InnerProductSpace ℂ (SmoothTestBundle m R b n hb hn P) := smoothLineSum_inner _ _ P
instance smoothTestBundle_smooth (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ (TestBundleSlot m R n))
      (SmoothTestBundle m R b n hb hn)
      𝓘(ℝ,ProjectiveProductModel (stageProjectiveDimensions m R b hb)) :=
  smoothLineSum_contMDiffVectorBundle _ _

theorem smoothTestBundle_finrank (m R b n : ℕ) (hb : b≤R) (hn : n≤b)
    (P : ProjectiveProduct (stageProjectiveDimensions m R b hb)) :
    Module.finrank ℂ (SmoothTestBundle m R b n hb hn P) = testRank m R n := by
  change Module.finrank ℂ (EuclideanSpace ℂ (TestBundleSlot m R n)) = _
  simpa [TestBundleSlot] using (sum_testMultiplicity (m := m) (hn.trans hb))

/-- The fresh block on Y_{j+1}, consisting of exactly a_{j+1,j+1}
occurrences of the hyperplane line of its last factor. -/
def smoothFreshCore (m R j : ℕ) (hj : j<R) :=
  smoothLineSumCore (stageProjectiveDimensions m R (j+1) hj)
    (fun _ : Fin (testMultiplicity m R (j+1) (Fin.last (j+1))) => some (Fin.last j))

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

def testReplacementMultiplicity (m R j : ℕ) (i : Fin (j+1)) : ℕ :=
  testMultiplicity m R (j+1) i.castSucc

def testReplacementCore (m R j : ℕ) (hj : j≤R) :=
  repeatedLineCore (fun i : Fin (j+1) => testLineCore m R (testSummandLineIndex hj i))
    (testReplacementMultiplicity m R j)

abbrev TestReplacementModel (m R j : ℕ) := RepeatedLineModel (testReplacementMultiplicity m R j)

theorem exists_testBundle_replacements {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ A : ∀ y, Fin 16 → TestBundle m R j hj.le y →ₗ[ℂ]
      (testReplacementCore m R j hj.le).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (TestBundle m R j hj.le) =>
        TotalSpace.mk' (TestReplacementModel m R j) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y) := by
  let C := fun i : Fin (j+1) => testLineCore m R (testSummandLineIndex hj.le i)
  let r := testReplacementMultiplicity m R j
  have hr : ∀ i,16*m≤r i := by
    intro i
    have hq := testMultiplicity_quarter (m := m) hj i
    have hl := testMultiplicity_lower_bound (m := m) hj i
    change 16*m≤testMultiplicity m R (j+1) i.castSucc
    omega
  have he : (fun i : Fin (j+1) => 4*r i) = testMultiplicity m R j := by
    funext i
    exact testMultiplicity_quarter hj i
  let P : (Fin (j+1) → ℕ) → Prop := fun D =>
    ∃ A : ∀ y, Fin 16 → (repeatedLineCore C D).Fiber y →ₗ[ℂ] (repeatedLineCore C r).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
        TotalSpace.mk' (RepeatedLineModel r) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y)
  have h : P (fun i => 4*r i) := exists_continuous_repeatedLine_replacements C m hm r hr
  exact Eq.mp (congrArg P he) h

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

def smoothReplacementCore (m R j : ℕ) (hj : j<R) :=
  repeatedLineCore (fun i : Fin (j+1) =>
    productLineCore (stageProjectiveDimensions m R (j+1) hj)
      (testSummandLineIndex (Nat.le_succ j) i)) (testReplacementMultiplicity m R j)

theorem exists_smoothTest_replacements {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ A : ∀ y, Fin 16 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothReplacementCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (TestReplacementModel m R j) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y) := by
  let C := fun i : Fin (j+1) => productLineCore (stageProjectiveDimensions m R (j+1) hj)
    (testSummandLineIndex (Nat.le_succ j) i)
  let r := testReplacementMultiplicity m R j
  have hr : ∀ i,16*m≤r i := by
    intro i
    have hq := testMultiplicity_quarter (m := m) hj i
    have hl := testMultiplicity_lower_bound (m := m) hj i
    change 16*m≤testMultiplicity m R (j+1) i.castSucc
    omega
  have he : (fun i : Fin (j+1) => 4*r i) = testMultiplicity m R j := by
    funext i
    exact testMultiplicity_quarter hj i
  let P : (Fin (j+1) → ℕ) → Prop := fun D =>
    ∃ A : ∀ y, Fin 16 → (repeatedLineCore C D).Fiber y →ₗ[ℂ] (repeatedLineCore C r).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
        TotalSpace.mk' (RepeatedLineModel r) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y)
  have h : P (fun i => 4*r i) := exists_continuous_repeatedLine_replacements C m hm r hr
  exact Eq.mp (congrArg P he) h

end Kaplansky

end

end OAI
