import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget
import OAI.Combinatorics.Progressions.Linear.SmoothSpatialKernelRegularity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem goodScalarKernelTuple_site_expansion {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    {L B : ℕ} {H : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ)) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA H L hH (by exact_mod_cast hL)
    let G := scalarSpatialIndexAllowance I B
    let K := smoothSpatialDensityLip s B
    ∃ (m : ℕ) (hm : 0 < m), m ≤ B ∧
      letI : NeZero m := ⟨hm.ne'⟩
      ∀ (C : Matrix (Unit ⊕ I) N ℤ) (ε : ℝ), 0 < ε →
        let r := spatialSiteRadius G K ε
        0 < r ∧
        ((∑ a : (Unit ⊕ I) → ZMod m, ∑ k : (Unit ⊕ I) → Fin (intervalSiteCount 1 r),
          ‖latticeStarMask (pivotFullImage A (Matrix.fromCols A' C)) m a *
            spatialStarDensity f (fun i => intervalSiteCenter 1 r (k i))‖) ≤
          (m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount 1 r : ℝ)^Fintype.card (Unit ⊕ I) *
            (G * smoothSpatialDensityCap s B)) ∧
        ∀ v : (Unit ⊕ I) → ℤ, (∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ 1) →
          ‖(maskedIntegerImageDensity A (Matrix.fromCols A' C) (fun _ => H) f v : ℂ) -
            spatialSiteApprox A (Matrix.fromCols A' C) m f H 1 r v‖ ≤ ε := by
  obtain ⟨hcap, hlip⟩ := smoothSpatialKernelDensity_bounds s x root hB hL hH hx hroot
  obtain ⟨m, hm, hmB, hp⟩ := goodScalarKernelTuple_selected_period s x root hx
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  intro C ε hε
  have hG : 0 ≤ scalarSpatialIndexAllowance I B := by unfold scalarSpatialIndexAllowance; positivity
  have hK := smoothSpatialDensityLip_nonneg s B
  have hr := spatialSiteRadius_pos hG hK hε
  have hindex : ((pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
      (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)).toAddSubgroup.index : ℝ) ≤
      scalarSpatialIndexAllowance I B := by
    unfold scalarSpatialIndexAllowance
    exact_mod_cast selectedSpatial_extended_index root (scalarCubeDifferenceMatrix x) s C hx.2
  have hpfull : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  refine ⟨hr, spatialSiteApprox_coefficient_sum _ _ m _ 1 _ hindex hcap, ?_⟩
  intro v hv
  have he := spatialSiteApprox_error _ _ m hpfull _ hlip hindex zero_lt_one hr H v hv
  rw [Real.coe_toNNReal _ hK] at he
  exact he.trans (spatialSiteRadius_error hG hK hε.le)

end Erdos3

end

end OAI
