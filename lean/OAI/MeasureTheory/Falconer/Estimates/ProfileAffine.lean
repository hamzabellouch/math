import OAI.MeasureTheory.Falconer.Geometry.ProfileGrid
import OAI.MeasureTheory.Falconer.Estimates.IntermediateProfiles

namespace OAI

namespace PlanarFalconer

theorem finiteRampProfile_affine_block (d c : ℕ → ℝ) (hd : Antitone d)
    {K i : ℕ} (hi : i < K) {u v : ℝ} (hu : d (i+1) ≤ u) (huv : u ≤ v) (hv : v ≤ d i) :
    finiteRampProfile d c K v - finiteRampProfile d c K u = c i*(v-u) := by
  classical
  simp only [finiteRampProfile,← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)]
  · simp only [intervalRamp,min_eq_left hv,min_eq_right (hu.trans huv),
      min_eq_left (huv.trans hv),min_eq_right hu]
    ring
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [intervalRamp_of_le (hd (Nat.le_succ j)) (hv.trans (hd (by omega : j+1 ≤ i))),
        intervalRamp_of_le (hd (Nat.le_succ j)) ((huv.trans hv).trans (hd (by omega : j+1 ≤ i)))]
      ring
    · rw [intervalRamp_of_ge (hd (Nat.le_succ j)) ((hd (by omega : i+1 ≤ j)).trans (hu.trans huv)),
        intervalRamp_of_ge (hd (Nat.le_succ j)) ((hd (by omega : i+1 ≤ j)).trans hu)]
      ring

theorem sourceProfile_affine_on_blocks (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N B : ℕ) (p : CellPath) {i : ℕ} (hi : i < N/B+1) :
    ∃ a b : ℝ, ∀ u : ℝ, (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) →
      sourceProfile Q μ N B p u = a*u+b := by
  let d := fun j => (blockDepth N B j:ℝ)
  let c := fun j => blockSlope (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) N B j p
  refine ⟨c i,sourceProfile Q μ N B p (d (i+1))-c i*d (i+1),?_⟩
  intro u hlo hhi
  have hh := finiteRampProfile_affine_block d c
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) hi (le_refl (d (i+1))) hlo hhi
  change sourceProfile Q μ N B p u - sourceProfile Q μ N B p (d (i+1)) = _ at hh
  linarith

theorem sourceProfile_adjusted_lipschitz (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath)
    {u v : ℝ} (hu : 0 ≤ u) (huN : u ≤ N) (hv : 0 ≤ v) (hvN : v ≤ N) :
    |(sourceProfile Q μ N B p v-v/(N:ℝ))-(sourceProfile Q μ N B p u-u/(N:ℝ))| ≤ |v-u|/(N:ℝ) := by
  classical
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)]
    exact regularizedProfile_adjusted_increment hN
      (show regularizationLeaves Q μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
      (regularizationLabel Q μ N B) hB p hu huv hvN
  · rw [abs_sub_comm (sourceProfile Q μ N B p v-v/(N:ℝ)),abs_sub_comm v u,
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact regularizedProfile_adjusted_increment hN
      (show regularizationLeaves Q μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
      (regularizationLabel Q μ N B) hB p hv hvu huN

end PlanarFalconer

end OAI
