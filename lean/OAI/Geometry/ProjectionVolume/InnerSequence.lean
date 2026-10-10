import OAI.Geometry.ProjectionVolume.FiniteApproximation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

open Set Metric Filter
open scoped Pointwise Topology

namespace Paper092

noncomputable def inscribedScale (m : ℕ) : ℝ := 1 - 1 / ((m : ℝ) + 2)

theorem inscribedScale_nonneg (m : ℕ) : 0 ≤ inscribedScale m := by
  unfold inscribedScale
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity : 0 < (m : ℝ) + 2)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem inscribedScale_lt_one (m : ℕ) : inscribedScale m < 1 := by
  unfold inscribedScale
  exact sub_lt_self _ (by positivity)

theorem exists_increasing_inscribed_finsets {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (hv : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K) :
    ∃ V : ℕ → Finset (Euclidean n),
      Monotone (fun m => convexHull ℝ (V m : Set (Euclidean n))) ∧
      (∀ m, convexHull ℝ (V m : Set (Euclidean n)) ⊆ K) ∧
      (∀ m, inscribedScale m • K ⊆ interior (convexHull ℝ (V m : Set (Euclidean n)))) ∧
      (∀ m, (0 : Euclidean n) ∈ interior (convexHull ℝ (V m : Set (Euclidean n)))) := by
  classical
  have hex := fun m => exists_inscribed_finset_sandwich hc hv h0
    (inscribedScale_nonneg m) (inscribedScale_lt_one m)
  choose t ht htK ht0 using hex
  let V : ℕ → Finset (Euclidean n) := fun m => (Finset.range (m + 1)).biUnion t
  have htV (i m : ℕ) (hi : i ≤ m) : (t i : Set (Euclidean n)) ⊆ V m := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hx⟩
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply convexHull_mono
    intro x hx
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr
      ((Finset.mem_range.mp hk).trans_le (by omega)), hx⟩
  · intro m
    apply convexHull_min _ hv
    intro x hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    exact htK i (subset_convexHull ℝ (t i : Set (Euclidean n)) hx)
  · intro m
    exact (ht m).trans (interior_mono (convexHull_mono (htV m m le_rfl)))
  · intro m
    exact interior_mono (convexHull_mono (htV m m le_rfl)) (ht0 m)

theorem add_closedBall_subset_dilate {n : ℕ} {P : Set (Euclidean n)}
    (hv : Convex ℝ P) {a ε : ℝ} (ha : 0 < a) (he : 0 ≤ ε)
    (hball : closedBall (0 : Euclidean n) a ⊆ P) :
    P + closedBall (0 : Euclidean n) ε ⊆ (1 + ε / a) • P := by
  have heq : (ε / a) • closedBall (0 : Euclidean n) a = closedBall 0 ε := by
    rw [smul_closedBall _ _ ha.le, smul_zero, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg he ha.le), div_mul_cancel₀ _ ha.ne']
  rw [← heq, hv.add_smul zero_le_one (div_nonneg he ha.le), one_smul]
  exact add_subset_add subset_rfl (image_mono hball)

theorem inscribed_thickening {n : ℕ} {K P : Set (Euclidean n)} {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (m : ℕ) (hP : inscribedScale m • K ⊆ P) :
    K ⊆ P + closedBall (0 : Euclidean n) (R / ((m : ℝ) + 2)) := by
  intro x hx
  refine ⟨inscribedScale m • x, hP ⟨x, hx, rfl⟩,
    (1 / ((m : ℝ) + 2)) • x, ?_, ?_⟩
  · simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / ((m : ℝ) + 2))]
    calc
      1 / ((m : ℝ) + 2) * ‖x‖ ≤ 1 / ((m : ℝ) + 2) * R :=
        mul_le_mul_of_nonneg_left (hR x hx) (by positivity)
      _ = R / ((m : ℝ) + 2) := by ring
  · change inscribedScale m • x + (1 / ((m : ℝ) + 2)) • x = x
    rw [← add_smul]
    simp [inscribedScale]

theorem tendsto_approximation_error (R : ℝ) :
    Tendsto (fun m : ℕ => R / ((m : ℝ) + 2)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_const_div_atTop_nhds_zero_nat R).comp (tendsto_add_atTop_nat 2)

theorem exists_inscribed_polytope_sequence {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (hv : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K) :
    ∃ (V : ℕ → Finset (Euclidean n)) (a R : ℝ),
      0 < a ∧ 0 < R ∧ K ⊆ closedBall 0 R ∧
      Monotone (fun m => convexHull ℝ (V m : Set (Euclidean n))) ∧
      (∀ m, closedBall (0 : Euclidean n) a ⊆ convexHull ℝ (V m : Set (Euclidean n))) ∧
      (∀ m, convexHull ℝ (V m : Set (Euclidean n)) ⊆ K ∧
        K ⊆ convexHull ℝ (V m : Set (Euclidean n)) + closedBall 0 (R / ((m : ℝ) + 2)) ∧
        convexHull ℝ (V m : Set (Euclidean n)) + closedBall 0 (R / ((m : ℝ) + 2)) ⊆
          (1 + (R / ((m : ℝ) + 2)) / a) • convexHull ℝ (V m : Set (Euclidean n))) ∧
      Tendsto (fun m : ℕ => R / ((m : ℝ) + 2)) atTop (𝓝 0) := by
  obtain ⟨V, hmono, hVK, hscale, hzero⟩ := exists_increasing_inscribed_finsets hc hv h0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp (hzero 0))
  obtain ⟨R, hRpos, hR⟩ := hc.isBounded.exists_pos_norm_le
  have hball0 : closedBall (0 : Euclidean n) (r / 2) ⊆ convexHull ℝ (V 0 : Set (Euclidean n)) :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hballm : ∀ m, closedBall (0 : Euclidean n) (r / 2) ⊆
      convexHull ℝ (V m : Set (Euclidean n)) :=
    fun m => hball0.trans (hmono (Nat.zero_le m))
  refine ⟨V, r / 2, R, half_pos hr, hRpos, ?_, hmono, hballm, ?_,
    tendsto_approximation_error R⟩
  · intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hR x hx
  · intro m
    exact ⟨hVK m, inscribed_thickening hR m ((hscale m).trans interior_subset),
      add_closedBall_subset_dilate (convex_convexHull ℝ _) (half_pos hr) (by positivity) (hballm m)⟩

end Paper092

end OAI
