import OAI.Geometry.IsometricImmersion.Assembly.TensorSeriesLocality

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry

theorem tensorPatchSum_eq_single_on_disjoint_carrier
    (η : ℕ → MetricField) (C : ℕ → Set Coord)
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (i : ℕ) {p : Coord} (hp : p ∈ C i) : tensorPatchSum η p = η i p := by
  change (∑' j, η j p) = η i p
  apply tsum_eq_single i
  intro j hji
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hji)
    (hsupp j (subset_tsupport (η j) hne)) hp

theorem tensorPatchSum_zero_off_carriers
    (η : ℕ → MetricField) (C : ℕ → Set Coord)
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    {p : Coord} (hp : ∀ j, p ∉ C j) : tensorPatchSum η p = 0 := by
  have hz (j : ℕ) : η j p = 0 := by
    by_contra hne
    exact hp j (hsupp j (subset_tsupport (η j) hne))
  change (∑' j, η j p) = 0
  simp only [hz, tsum_zero]

theorem tensorPatchSum_posDef_of_disjoint
    (η : ℕ → MetricField) (C : ℕ → Set Coord)
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    {g : MetricField} {U : Set Coord}
    (hg : ∀ p ∈ U, (g p).PosDef)
    (hlocal : ∀ j, ∀ p ∈ U ∩ C j, ((g + η j) p).PosDef) :
    ∀ p ∈ U, ((g + tensorPatchSum η) p).PosDef := by
  intro p hp
  by_cases hex : ∃ j, p ∈ C j
  · obtain ⟨j, hj⟩ := hex
    change (g p + tensorPatchSum η p).PosDef
    rw [tensorPatchSum_eq_single_on_disjoint_carrier η C hsupp hdisjoint j hj]
    exact hlocal j p ⟨hp, hj⟩
  · have hout : ∀ j, p ∉ C j := fun j hj => hex ⟨j, hj⟩
    change (g p + tensorPatchSum η p).PosDef
    rw [tensorPatchSum_zero_off_carriers η C hsupp hout, add_zero]
    exact hg p hp

theorem tensorPatchSum_smoothPositive_of_disjoint
    (η : ℕ → MetricField) (C : ℕ → Set Coord) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hC : ∀ j, IsCompact (C j))
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (hlocal : ∀ j, ∀ p ∈ U ∩ C j, ((g + η j) p).PosDef) :
    SmoothPositiveOn (g + tensorPatchSum η) U := by
  have hc (j : ℕ) : HasCompactSupport (η j) :=
    (hC j).of_isClosed_subset (isClosed_tsupport (η j)) (hsupp j)
  exact smoothPositive_metric_add_of_tensor_contDiff hg
    (tensorPatchSum_contDiff η ε hη hc hbound)
    (tensorPatchSum_posDef_of_disjoint η C hsupp hdisjoint hg.2 hlocal)

theorem tensorPatchSum_preserves_disk_of_disjoint
    (η : ℕ → MetricField) (C : ℕ → Set Coord) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hC : ∀ j, IsCompact (C j))
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hlocal : ∀ j, ∀ p ∈ U ∩ C j, ((g + η j) p).PosDef)
    (n : ℕ) (hDU : accumulatingDisk n ⊆ U)
    (havoid : ∀ j, Disjoint (C j) (accumulatingDisk n)) :
    ∀ p ∈ accumulatingDisk n,
      (∀ k : ℕ, iteratedFDeriv ℝ k (tensorPatchSum η) p = 0) ∧
      (∀ ds : List (Fin 2), ∀ a b : Fin 2,
        iteratedCoordPartial ds (fun q => (g + tensorPatchSum η) q a b) p =
          iteratedCoordPartial ds (fun q => g q a b) p) ∧
      gaussianCurvature (g + tensorPatchSum η) p = gaussianCurvature g p := by
  have hc (j : ℕ) : HasCompactSupport (η j) :=
    (hC j).of_isClosed_subset (isClosed_tsupport (η j)) (hsupp j)
  exact tensorPatchSum_preserves_closed_disk η ε hη hc hbound hg hU
    (tensorPatchSum_posDef_of_disjoint η C hsupp hdisjoint hg.2 hlocal) n hDU
    (fun j => (havoid j).mono_left (hsupp j))

end SmoothLocal.Geometry

end

end OAI
