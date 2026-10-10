import OAI.Geometry.RCD.Coordinates.PatchCover
import OAI.Analysis.RCDHeat.VolumeComparison

namespace OAI

/-! # Properness from the actual curvature-dimension volume bound

The existing `FullCD.ball_ratio` theorem bounds the mass of every small
ball centered in a bounded region from below. Disjoint small balls therefore
bound every separated set. The resulting finite nets prove total boundedness;
completeness then gives properness. No compactness hypothesis is added.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
private theorem separated_encard_le_of_finset_bound {A : Set X} {r : ℝ≥0} {N : ℕ}
    (hbound : ∀ s : Finset X, (s : Set X) ⊆ A →
      (s : Set X).Pairwise (fun x y => (r : ℝ) ≤ dist x y) → s.card ≤ N)
    {C : Set X} (hCA : C ⊆ A) (hC : Metric.IsSeparated r C) : C.encard ≤ N := by
  classical
  have hsbound (s : Finset X) (hsC : (s : Set X) ⊆ C) : s.card ≤ N := by
    apply hbound s (hsC.trans hCA)
    intro x hx y hy hxy
    have hh := hC (hsC hx) (hsC hy) hxy
    have hd : r < nndist x y := by
      simpa only [edist_nndist, ENNReal.coe_lt_coe] using hh
    exact_mod_cast hd.le
  have hfin : C.Finite := by
    by_contra hinf
    obtain ⟨t, htC, htfin, htcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf (N + 1)
    have hh := hsbound htfin.toFinset (by simpa only [htfin.coe_toFinset] using htC)
    rw [← Set.ncard_coe_finset, htfin.coe_toFinset, htcard] at hh
    omega
  rw [hfin.encard_eq_coe_toFinset_card]
  exact_mod_cast hsbound hfin.toFinset (by simp)

/-- Every bounded ball is totally bounded, directly from CD volume comparison. -/
theorem NoncollapsedRCD.totallyBounded_closedBall {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) (R : ℝ) :
    TotallyBounded (closedBall p R) := by
  classical
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  by_cases hR : R < 0
  · simp only [closedBall_eq_empty.mpr hR]
    exact totallyBounded_empty
  have hR0 : 0 ≤ R := le_of_not_gt hR
  apply Metric.totallyBounded_iff.mpr
  intro epsilon hepsilon
  let r : ℝ≥0 := ⟨min (epsilon / 2) 1, le_of_lt (lt_min (by positivity) zero_lt_one)⟩
  have hr : 0 < (r : ℝ) := lt_min (by positivity) zero_lt_one
  have hr1 : (r : ℝ) ≤ 1 := min_le_right _ _
  have hre : (r : ℝ) < epsilon := (min_le_left _ _).trans_lt (by linarith)
  let T := R + 1
  have hT : 0 < T := by dsimp only [T]; linarith only [hR0]
  have hrT : (r : ℝ) / 2 ≤ T := by dsimp only [T]; linarith only [hr1, hR0]
  let b := distortionFloor K n (2 * T) ((r : ℝ) / 2 / T) ^ n
  have hb0 : b ≠ 0 := by
    dsimp only [b, distortionFloor]
    exact pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have hbt : b ≠ ∞ := by
    dsimp only [b, distortionFloor]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  let v := (b * (hausdorff n X) (ball p 1)).toReal
  have hv : 0 < v := ENNReal.toReal_pos
    (mul_ne_zero hb0 (ne_of_gt (hX.fullSupport p 1 zero_lt_one)))
    (ENNReal.mul_ne_top hbt (hX.finiteOnBounded _ isBounded_ball).ne)
  have hlower (y : X) (hy : y ∈ closedBall p R) :
      v ≤ (hausdorff n X).real (ball y ((r : ℝ) / 2)) := by
    have hsub : ball p 1 ⊆ ball y T := by
      apply Metric.ball_subset_ball'
      change 1 + dist p y ≤ R + 1
      have hh : dist y p ≤ R := hy
      rw [dist_comm]
      linarith only [hh]
    have hratio := hX.cd.ball_ratio (hausdorff n X) K n hX.fullSupport hX.finiteOnBounded
      hn y ((r : ℝ) / 2) T (by positivity) hrT
    have hh : b * (hausdorff n X) (ball p 1) ≤
        (hausdorff n X) (ball y ((r : ℝ) / 2)) :=
      (mul_le_mul' le_rfl (measure_mono hsub)).trans hratio
    exact ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne hh
  let N : ℕ := ⌈(hausdorff n X).real (ball p (R + (r : ℝ) / 2)) / v⌉₊
  have hcard (s : Finset X) (hs : (s : Set X) ⊆ closedBall p R)
      (hsep : (s : Set X).Pairwise (fun x y => (r : ℝ) ≤ dist x y)) : s.card ≤ N := by
    have hh := separated_card_mul_volume_le (hausdorff n X) s p hsep
      (fun y hy => hs hy) (fun y hy => hlower y (hs hy))
      (hX.finiteOnBounded _ isBounded_ball).ne
    have hb := (le_div_iff₀ hv).mpr hh
    exact_mod_cast hb.trans (Nat.le_ceil _)
  have hpacking : Metric.packingNumber r (closedBall p R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (N : ℕ∞) ≠ ⊤)
    exact iSup_le fun C => iSup_le fun hCA => iSup_le fun hC =>
      separated_encard_le_of_finset_bound hcard hCA hC
  let C := Metric.maximalSeparatedSet r (closedBall p R)
  have hfinite : C.Finite := finite_maximalSeparatedSet r _
  have hcover := Metric.isCover_maximalSeparatedSet hpacking
  refine ⟨C, hfinite, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover hx
  change edist x y ≤ (r : ℝ≥0∞) at hxy
  refine mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  have hh : nndist x y ≤ r := by
    simpa only [edist_nndist, ENNReal.coe_le_coe] using hxy
  have hd : dist x y ≤ (r : ℝ) := by exact_mod_cast hh
  exact hd.trans_lt hre

/-- The proper-space assumption of the conditional chart theorem is itself
an RCD consequence in the manuscript's dimension range. -/
theorem NoncollapsedRCD.properSpace {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) : ProperSpace X := by
  let := hX.complete
  refine ⟨fun p R => ?_⟩
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨hX.totallyBounded_closedBall hn p R, isClosed_closedBall.isComplete⟩

end RegularPointCoordinates

end

end OAI
