import OAI.Geometry.BundleTests.Smooth
import OAI.Geometry.ComplexBundle.CoordinatesMetric

namespace OAI

noncomputable section

/-! Fresh bundle maps and assembly of the test-bundle step. -/

section
open Bundle Topology Module
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

theorem testBundleSlot_card {m R j : ℕ} (hj : j≤R) :
    Fintype.card (TestBundleSlot m R j) = testRank m R j := by
  simpa [TestBundleSlot] using (sum_testMultiplicity (m := m) hj)

abbrev TestSourceCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
    (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))

abbrev TestFreshRank (m R j : ℕ) := testMultiplicity m R (j+1) (Fin.last (j+1))

abbrev TestFreshCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (fun _ : Fin (TestFreshRank m R j) => some (Fin.last j))
    (TestFreshRank m R j) (Fintype.card_fin _)

theorem exists_test_eight_fresh_bundle_maps {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ T : Fin 8 → ∀ y, TestSourceCoordinates m R j hj y →L[ℂ] TestFreshCoordinates m R j hj y,
      (∀ i, ContMDiff 𝓘(ℝ,SmoothPrefixModel m R j hj)
        (𝓘(ℝ,SmoothPrefixModel m R j hj).prod
          𝓘(ℝ,(Fin (testRank m R j) → ℂ) →L[ℝ] (Fin (TestFreshRank m R j) → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin (testRank m R j) → ℂ) →L[ℝ]
          (Fin (TestFreshRank m R j) → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y (S : Submodule ℂ (TestSourceCoordinates m R j hj y)), m<finrank ℂ S →
        2*finrank ℂ S≤finrank ℂ (⨆ i, S.map (T i y).toLinearMap :
          Submodule ℂ (TestFreshCoordinates m R j hj y)) := by
  apply Incidence.exists_eight_fresh_bundle_maps
  · unfold testRank
    positivity
  · exact testMultiplicity_fresh hj
  · exact smoothPrefix_incidence_margin hm hj

end Kaplansky

end

section
open Bundle Topology Module
namespace Kaplansky
open ComplexGrassmann

/-- The finite-coordinate incidence maps give genuine continuous maps on
the original Hilbert-sum presentation of E_j and its fresh block. -/
theorem exists_smoothTest_freshMaps {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ A : ∀ y, Fin 8 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothFreshCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (EuclideanSpace ℂ (Fin (TestFreshRank m R j))) z.proj (A z.proj i z.2))) ∧
      ∀ y (S : Submodule ℂ (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y)),
        m<finrank ℂ S → 2*finrank ℂ S≤finrank ℂ
          (⨆ i, S.map (A y i) : Submodule ℂ ((smoothFreshCore m R j hj).Fiber y)) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_eight_fresh_bundle_maps hm hj
  let e := finiteCoordinateEquiv (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj) (m := m))
  let f := finiteCoordinateEquiv (TestFreshRank m R j) (Fintype.card_fin (TestFreshRank m R j))
  let a := fun y => (show SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y ≃ₗ[ℂ]
    TestSourceCoordinates m R j hj y from e.toLinearEquiv)
  let b := fun y => (show (smoothFreshCore m R j hj).Fiber y ≃ₗ[ℂ]
    TestFreshCoordinates m R j hj y from f.toLinearEquiv)
  let A := fun y i => (b y).symm.toLinearMap.comp ((T i y).toLinearMap.comp (a y).toLinearMap)
  refine ⟨A,?_,?_⟩
  · intro i
    have hc : Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (TestFreshRank m R j) → ℂ) z.proj (T i z.proj z.2)) :=
      ((hT i).continuous.comp (FiberBundle.continuous_proj _ _)).clm_bundle_apply continuous_id
    let H := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
      (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))
    let G := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun _ : Fin (TestFreshRank m R j) => some (Fin.last j))
      (TestFreshRank m R j) (Fintype.card_fin _)
    exact G.symm.continuous.comp (hc.comp H.continuous)
  · intro y S hS
    have h := hExp y (S.map (a y).toLinearMap) (by simpa only [(a y).finrank_map_eq] using hS)
    rw [(a y).finrank_map_eq] at h
    have he : (⨆ i, S.map (A y i)) =
        (⨆ i, (S.map (a y).toLinearMap).map (T i y).toLinearMap).map (b y).symm.toLinearMap := by
      rw [Submodule.map_iSup]
      apply iSup_congr
      intro i
      rw [Submodule.map_comp,Submodule.map_comp]
    rw [he,(b y).symm.finrank_map_eq]
    exact h

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

abbrev TestNextSlot (m R j : ℕ) :=
  (Σ i : Fin (j+1), Fin (testReplacementMultiplicity m R j i)) ⊕ Fin (TestFreshRank m R j)

def testNextLabel (m R j : ℕ) : TestNextSlot m R j → Option (Fin (j+1)) :=
  Sum.elim (fun s => testSummandLineIndex (Nat.le_succ j) s.1) (fun _ => some (Fin.last j))

/-- E_{j+1} presented as the direct sum of its replacement and fresh blocks. -/
def smoothNextCore (m R j : ℕ) (hj : j<R) :=
  smoothLineSumCore (stageProjectiveDimensions m R (j+1) hj) (testNextLabel m R j)

theorem testNextSlot_card {m R j : ℕ} (hj : j<R) :
    Fintype.card (TestNextSlot m R j) = testRank m R (j+1) := by
  have h := sum_testMultiplicity (m := m) hj
  rw [Fin.sum_univ_castSucc] at h
  change Fintype.card ((Σ i : Fin (j+1), Fin (testReplacementMultiplicity m R j i)) ⊕
    Fin (TestFreshRank m R j)) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  calc
    _ = (∑ i : Fin (j+1), testReplacementMultiplicity m R j i) + TestFreshRank m R j := by
      apply congrArg₂ (fun a b : ℕ => a + b)
      · exact Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)
      · exact Fintype.card_fin _
    _ = _ := h

theorem exists_test_twentyFour_expanding_maps {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    ∃ T : ∀ y, Fin 24 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothNextCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (EuclideanSpace ℂ (TestNextSlot m R j)) z.proj (T z.proj i z.2))) ∧
      ∀ y, IntrinsicExpanding (T y) := by
  obtain ⟨A,hA,heA⟩ := exists_smoothTest_replacements hm hj
  obtain ⟨B,hB,heB⟩ := exists_smoothTest_freshMaps hm hj
  let L := fun u : TestNextSlot m R j =>
    productLineCore (stageProjectiveDimensions m R (j+1) hj) (testNextLabel m R j u)
  let T : ∀ y, Fin 24 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothNextCore m R j hj).Fiber y := fun y q => Fin.addCases
    (motive := fun _ : Fin (16+8) => SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ] (smoothNextCore m R j hj).Fiber y)
    (fun i => (lineSumInl L y).comp (A y i))
    (fun i => (lineSumInr L y).comp (B y i)) q
  refine ⟨T,?_,?_⟩
  · intro i
    refine Fin.addCases (m := 16) (n := 8) ?_ ?_ i
    · intro a
      have ht (y) : T y (Fin.castAdd 8 a) = (lineSumInl L y).comp (A y a) :=
        Fin.addCases_left a
      apply ((continuous_lineSumInl L).comp (hA a)).congr
      intro z
      apply congrArg (TotalSpace.mk' _ z.proj)
      exact (congrArg (fun F => F z.2) (ht z.proj)).symm
    · intro b
      have ht (y) : T y (Fin.natAdd 16 b) = (lineSumInr L y).comp (B y b) :=
        Fin.addCases_right b
      apply ((continuous_lineSumInr L).comp (hB b)).congr
      intro z
      apply congrArg (TotalSpace.mk' _ z.proj)
      exact (congrArg (fun F => F z.2) (ht z.proj)).symm
  · intro y
    let : FiniteDimensional ℂ ((finiteLineSumCore L).Fiber y) :=
      inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ (TestNextSlot m R j)))
    exact combined_expanding m (A y) (B y) (lineSumInl L y) (lineSumInr L y)
      (lineSumInl_injective L y) (lineSumInr_injective L y) (heA y) (heB y)

end Kaplansky

end

end OAI
