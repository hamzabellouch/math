import OAI.Geometry.IsometricImmersion.Assembly.FlatPatchSum
import OAI.Geometry.IsometricImmersion.Calculus.MetricTwoJet
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm
import Mathlib.Analysis.Matrix.Normed

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry

abbrev TensorMatrix := Matrix (Fin 2) (Fin 2) ℝ

namespace TensorJetCalculus

def coefficient (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))

theorem coefficient_contDiff {η : MetricField} (hη : ContDiff ℝ ∞ η) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => η p i j) :=
  (coefficient i j).contDiff.comp hη

theorem coefficient_iteratedFDeriv {η : MetricField} (hη : ContDiff ℝ ∞ η)
    (k : ℕ) (p : Coord) (v : Fin k → Coord) (i j : Fin 2) :
    iteratedFDeriv ℝ k (fun q => η q i j) p v =
      (iteratedFDeriv ℝ k η p v) i j := by
  change iteratedFDeriv ℝ k (coefficient i j ∘ η) p v =
    coefficient i j (iteratedFDeriv ℝ k η p v)
  have he := (coefficient i j).iteratedFDeriv_comp_left (x := p) (i := k)
    hη.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun L : Coord [×k]→L[ℝ] ℝ => L v) he

theorem coefficient_coord_word {η : MetricField} (hη : ContDiff ℝ ∞ η)
    (ds : List (Fin 2)) (p : Coord) (i j : Fin 2) :
    iteratedCoordPartial ds (fun q => η q i j) p =
      (iteratedFDeriv ℝ ds.length η p (coordinateDirections ds)) i j := by
  rw [iteratedCoordPartial_eq_jet (coefficient_contDiff hη i j).contDiffOn
    isOpen_univ ds (mem_univ p)]
  exact coefficient_iteratedFDeriv hη ds.length p (coordinateDirections ds) i j

end TensorJetCalculus

def tensorPatchSum (η : ℕ → MetricField) : MetricField := flatPatchSum η

theorem tensorPatchSum_summable (η : ℕ → MetricField) (ε : ℝ)
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j) (p : Coord) :
    Summable (fun j => η j p) :=
  flatPatchSum_summable η ε hbound p

theorem tensorPatchSum_contDiff (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j) :
    ContDiff ℝ ∞ (tensorPatchSum η) :=
  flatPatchSum_contDiff η ε hη hc hbound

theorem tensorPatchSum_jets_zero_of_jets_zero
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {p : Coord} (hzero : ∀ j k : ℕ, iteratedFDeriv ℝ k (η j) p = 0) (k : ℕ) :
    iteratedFDeriv ℝ k (tensorPatchSum η) p = 0 := by
  rw [tensorPatchSum, flatPatchSum_iteratedFDeriv η ε hη hc hbound k p]
  simp only [hzero, tsum_zero]

theorem tensorPatchSum_jets_zero_off_each_support
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {p : Coord} (hp : ∀ j, p ∉ tsupport (η j)) (k : ℕ) :
    iteratedFDeriv ℝ k (tensorPatchSum η) p = 0 :=
  flatPatchSum_all_jets_zero η ε hη hc hbound hp k

theorem tensorPatchSum_jets_eq_single
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    (i : ℕ) {p : Coord} (hp : ∀ j, j ≠ i → p ∉ tsupport (η j)) (k : ℕ) :
    iteratedFDeriv ℝ k (tensorPatchSum η) p = iteratedFDeriv ℝ k (η i) p := by
  rw [tensorPatchSum, flatPatchSum_iteratedFDeriv η ε hη hc hbound k p]
  apply tsum_eq_single i
  intro j hji
  by_contra hne
  exact hp j hji ((support_iteratedFDeriv_subset (𝕜 := ℝ) k) hne)

theorem metric_add_coordinate_jets_eq_of_tensor_jets
    {g τ σ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hσ : ContDiff ℝ ∞ σ)
    (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = iteratedFDeriv ℝ k σ p)
    (ds : List (Fin 2)) (i j : Fin 2) :
    iteratedCoordPartial ds (fun q => (g + τ) q i j) p =
      iteratedCoordPartial ds (fun q => (g + σ) q i j) p := by
  change iteratedCoordPartial ds (fun q => g q i j + τ q i j) p =
    iteratedCoordPartial ds (fun q => g q i j + σ q i j) p
  rw [CoordinateBound.iterated_add (hg.1 i j)
      (TensorJetCalculus.coefficient_contDiff hτ i j).contDiffOn hU ds hp,
    CoordinateBound.iterated_add (hg.1 i j)
      (TensorJetCalculus.coefficient_contDiff hσ i j).contDiffOn hU ds hp,
    TensorJetCalculus.coefficient_coord_word hτ ds p i j,
    TensorJetCalculus.coefficient_coord_word hσ ds p i j, hjets ds.length]

theorem metric_add_coordinate_jets_eq_of_zero_tensor_jets
    {g τ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = 0)
    (ds : List (Fin 2)) (i j : Fin 2) :
    iteratedCoordPartial ds (fun q => (g + τ) q i j) p =
      iteratedCoordPartial ds (fun q => g q i j) p := by
  change iteratedCoordPartial ds (fun q => g q i j + τ q i j) p = _
  rw [CoordinateBound.iterated_add (hg.1 i j)
    (TensorJetCalculus.coefficient_contDiff hτ i j).contDiffOn hU ds hp,
    TensorJetCalculus.coefficient_coord_word hτ ds p i j, hjets ds.length]
  simp

theorem smoothPositive_metric_add_of_tensor_contDiff
    {g τ : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (hτ : ContDiff ℝ ∞ τ) (hpos : ∀ p ∈ U, ((g + τ) p).PosDef) :
    SmoothPositiveOn (g + τ) U := by
  refine ⟨?_, hpos⟩
  intro i j
  exact (hg.1 i j).add (TensorJetCalculus.coefficient_contDiff hτ i j).contDiffOn

theorem gaussianCurvature_add_eq_of_zero_tensor_jets
    {g τ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hpos : ∀ q ∈ U, ((g + τ) q).PosDef)
    (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = 0) :
    gaussianCurvature (g + τ) p = gaussianCurvature g p := by
  have hwords := metric_add_coordinate_jets_eq_of_zero_tensor_jets hg hU hp hτ hjets
  apply gaussianCurvature_eq_of_twoJet
    (smoothPositive_metric_add_of_tensor_contDiff hg hτ hpos) hg hU hp
  · ext i j
    exact hwords [] i j
  · intro d i j
    exact hwords [d] i j
  · intro d e i j
    exact hwords [d, e] i j

theorem gaussianCurvature_add_eq_of_tensor_jets
    {g τ σ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hσ : ContDiff ℝ ∞ σ)
    (hposτ : ∀ q ∈ U, ((g + τ) q).PosDef)
    (hposσ : ∀ q ∈ U, ((g + σ) q).PosDef)
    (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = iteratedFDeriv ℝ k σ p) :
    gaussianCurvature (g + τ) p = gaussianCurvature (g + σ) p := by
  have hwords := metric_add_coordinate_jets_eq_of_tensor_jets hg hU hp hτ hσ hjets
  apply gaussianCurvature_eq_of_twoJet
    (smoothPositive_metric_add_of_tensor_contDiff hg hτ hposτ)
    (smoothPositive_metric_add_of_tensor_contDiff hg hσ hposσ) hU hp
  · ext i j
    exact hwords [] i j
  · intro d i j
    exact hwords [d] i j
  · intro d e i j
    exact hwords [d, e] i j

theorem tensorPatchSum_curvature_eq_of_zero_summand_jets
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {g : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hpos : ∀ q ∈ U, ((g + tensorPatchSum η) q).PosDef)
    (hzero : ∀ j k : ℕ, iteratedFDeriv ℝ k (η j) p = 0) :
    gaussianCurvature (g + tensorPatchSum η) p = gaussianCurvature g p :=
  gaussianCurvature_add_eq_of_zero_tensor_jets hg hU hp
    (tensorPatchSum_contDiff η ε hη hc hbound) hpos
    (tensorPatchSum_jets_zero_of_jets_zero η ε hη hc hbound hzero)

theorem tensorPatchSum_metric_jets_off_carriers
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    (C : ℕ → Set Coord) (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    {g : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (houtside : ∀ j, p ∉ C j) (ds : List (Fin 2)) (a b : Fin 2) :
    iteratedCoordPartial ds (fun q => (g + tensorPatchSum η) q a b) p =
      iteratedCoordPartial ds (fun q => g q a b) p :=
  metric_add_coordinate_jets_eq_of_zero_tensor_jets hg hU hp
    (tensorPatchSum_contDiff η ε hη hc hbound)
    (tensorPatchSum_jets_zero_off_each_support η ε hη hc hbound
      (fun j hj => houtside j (hsupp j hj))) ds a b

theorem tensorPatchSum_preserves_closed_disk
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hpos : ∀ q ∈ U, ((g + tensorPatchSum η) q).PosDef)
    (d : ℕ) (hDU : accumulatingDisk d ⊆ U)
    (hdisjoint : ∀ j, Disjoint (tsupport (η j)) (accumulatingDisk d)) :
    ∀ p ∈ accumulatingDisk d,
      (∀ k : ℕ, iteratedFDeriv ℝ k (tensorPatchSum η) p = 0) ∧
      (∀ ds : List (Fin 2), ∀ a b : Fin 2,
        iteratedCoordPartial ds (fun q => (g + tensorPatchSum η) q a b) p =
          iteratedCoordPartial ds (fun q => g q a b) p) ∧
      gaussianCurvature (g + tensorPatchSum η) p = gaussianCurvature g p := by
  intro p hp
  have hnot (j : ℕ) : p ∉ tsupport (η j) := fun hj =>
    Set.disjoint_left.mp (hdisjoint j) hj hp
  have hjets := tensorPatchSum_jets_zero_off_each_support η ε hη hc hbound hnot
  have hsmooth := tensorPatchSum_contDiff η ε hη hc hbound
  exact ⟨hjets,
    metric_add_coordinate_jets_eq_of_zero_tensor_jets hg hU (hDU hp) hsmooth hjets,
    gaussianCurvature_add_eq_of_zero_tensor_jets hg hU (hDU hp) hsmooth hpos hjets⟩

theorem tensorPatchSum_zero_curvature_on_disk_frontier
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hpos : ∀ q ∈ U, ((g + tensorPatchSum η) q).PosDef)
    (d : ℕ) (hDU : accumulatingDisk d ⊆ U)
    (hdisjoint : ∀ j, Disjoint (tsupport (η j)) (accumulatingDisk d))
    (hK : ∀ p ∈ frontier (accumulatingDisk d), gaussianCurvature g p = 0) :
    ∀ p ∈ frontier (accumulatingDisk d), gaussianCurvature (g + tensorPatchSum η) p = 0 := by
  intro p hp
  have hpD : p ∈ accumulatingDisk d := by
    simpa only [(accumulatingDisk_isCompact d).isClosed.closure_eq] using
      frontier_subset_closure hp
  rw [(tensorPatchSum_preserves_closed_disk η ε hη hc hbound hg hU hpos d hDU
    hdisjoint p hpD).2.2]
  exact hK p hp

theorem tensorPatchSum_metric_jets_eq_single_off_other_carriers
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    (C : ℕ → Set Coord) (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    {g : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (i : ℕ) (houtside : ∀ j, j ≠ i → p ∉ C j)
    (ds : List (Fin 2)) (a b : Fin 2) :
    iteratedCoordPartial ds (fun q => (g + tensorPatchSum η) q a b) p =
      iteratedCoordPartial ds (fun q => (g + η i) q a b) p :=
  metric_add_coordinate_jets_eq_of_tensor_jets hg hU hp
    (tensorPatchSum_contDiff η ε hη hc hbound) (hη i)
    (tensorPatchSum_jets_eq_single η ε hη hc hbound i
      (fun j hji hj => houtside j hji (hsupp j hj))) ds a b

end SmoothLocal.Geometry

end

end OAI
