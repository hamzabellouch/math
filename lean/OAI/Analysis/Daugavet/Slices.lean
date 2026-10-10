import OAI.Analysis.Daugavet.LowerBounds

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX uY

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma exists_unit_near_opNorm (T : X →L[ℝ] Y) {r : ℝ} (hr : 0 ≤ r) (hrT : r < ‖T‖) :
    ∃ y : X, ‖y‖ = 1 ∧ r < ‖T y‖ := by
  obtain ⟨u, hu, hTu⟩ := T.exists_lt_apply_of_lt_opNorm hrT
  have hu0 : u ≠ 0 := by
    intro heq
    simp only [heq, map_zero, norm_zero] at hTu
    linarith
  have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  refine ⟨‖u‖⁻¹ • u, norm_smul_inv_norm hu0, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)]
  have hinv : 1 ≤ ‖u‖⁻¹ := (one_le_inv₀ hnpos).mpr hu.le
  have := mul_le_mul_of_nonneg_right hinv (norm_nonneg (T u))
  exact hTu.trans_le (by simpa only [one_mul] using this)

lemma daugavet_normalized_slice (hd : Daugavet X) {w : X} (hw : ‖w‖ = 1)
    (ell : X →L[ℝ] ℝ) (hell : ‖ell‖ = 1) {α ρ : ℝ} (hα : α < 1) (hρ : 0 < ρ) :
    ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖ := by
  let η := min (1 - α) (min (ρ / 2) 1) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηα : η < 1 - α := by
    have := min_le_left (1 - α) (min (ρ / 2) 1)
    dsimp [η] at *; linarith
  have hηρ : 2 * η < ρ := by
    have := (min_le_right (1 - α) (min (ρ / 2) 1)).trans (min_le_left _ _)
    dsimp [η] at *; linarith
  have hη1 : η < 1 := by
    have := (min_le_right (1 - α) (min (ρ / 2) 1)).trans (min_le_right _ _)
    dsimp [η] at *; linarith
  let T : X →L[ℝ] X := ContinuousLinearMap.id ℝ X + ell.smulRight w
  have hT : ‖T‖ = 2 := by
    change ‖ContinuousLinearMap.id ℝ X + ell.smulRight w‖ = 2
    rw [hd ell w, ContinuousLinearMap.norm_smulRight_apply, hell, hw]
    norm_num
  obtain ⟨u, hu, hval⟩ := exists_unit_near_opNorm T (show 0 ≤ 2 - η by linarith)
    (show 2 - η < ‖T‖ by rw [hT]; linarith)
  obtain ⟨y, hy, hsign, hyval⟩ : ∃ y : X, ‖y‖ = 1 ∧ 0 ≤ ell y ∧
      2 - η < ‖y + ell y • w‖ := by
    by_cases he : 0 ≤ ell u
    · exact ⟨u, hu, he, hval⟩
    · refine ⟨-u, by simpa using hu, by simpa using (neg_nonneg.mpr (le_of_not_ge he)), ?_⟩
      change 2 - η < ‖T (-u)‖
      simpa only [map_neg, norm_neg] using hval
  have he1 : ell y ≤ 1 := by
    have hb := ell.le_opNorm y
    rw [hell, hy, one_mul, Real.norm_eq_abs] at hb
    exact le_trans (le_abs_self _) hb
  have hnear : 1 - η < ell y := by
    have hb := norm_add_le y (ell y • w)
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsign, hw, mul_one] at hb
    linarith
  refine ⟨y, hy, by linarith, ?_⟩
  have hid : y + ell y • w = (w + y) + (ell y - 1) • w := by module
  have hb := norm_add_le (w + y) ((ell y - 1) • w)
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he1), hw,
    mul_one] at hb
  linarith

/-- Forward half of the actual rank-one/slice equivalence, with a unit-sphere witness. -/
theorem daugavet_unitSlice (hd : Daugavet X) : UnitSliceProperty X := by
  intro w hw ell α hne ρ hρ
  obtain ⟨u, hu, hau⟩ := hne
  by_cases he0 : ell = 0
  · have hα : α < 0 := by simpa [he0] using hau
    refine ⟨w, hw, by simpa [he0] using hα, ?_⟩
    have htwo : ‖w + w‖ = 2 := by rw [← two_smul ℝ w, norm_smul, hw]; norm_num
    rw [htwo]; linarith
  · have hn : 0 < ‖ell‖ := norm_pos_iff.mpr he0
    have hα : α < ‖ell‖ := by
      have hbound := ell.le_opNorm u
      have := le_abs_self (ell u)
      rw [Real.norm_eq_abs] at hbound
      nlinarith
    have hnormalized : ‖‖ell‖⁻¹ • ell‖ = 1 := norm_smul_inv_norm he0
    obtain ⟨y, hy, hslice, hfar⟩ := daugavet_normalized_slice hd hw (‖ell‖⁻¹ • ell)
      hnormalized ((div_lt_one hn).mpr hα) hρ
    refine ⟨y, hy, ?_, hfar⟩
    change α / ‖ell‖ < ‖ell‖⁻¹ * ell y at hslice
    rw [← div_eq_inv_mul] at hslice
    exact (div_lt_div_iff_of_pos_right hn).mp hslice

end ExactModuli

namespace ExactModuli
open scoped RealInnerProductSpace
variable {Y : Type uY} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma exposed_support_approx {K : Set Y} (hK : IsCompact K) {q : Y} (hq : q ∈ K)
    (ell : Y →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ K.exposedPoints ℝ, ell q - ε < ell p := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  let c : ℝ := ε / (M ^ 2 + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_eq : c * (M ^ 2 + 1) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨q, hq⟩
    ((ell.continuous.add (continuous_const.mul (continuous_norm.pow 2))).continuousOn :
      ContinuousOn (fun z : Y => ell z + c * ‖z‖ ^ 2) K)
  have hpM : ‖p‖ ^ 2 ≤ M ^ 2 := by nlinarith [hM p hp, norm_nonneg p]
  refine ⟨p, ⟨hp, ell + (2 * c) • innerSL ℝ p, ?_⟩, ?_⟩
  · intro z hz
    have hcomp := hmax hz
    change ell z + c * ‖z‖ ^ 2 ≤ ell p + c * ‖p‖ ^ 2 at hcomp
    have hsq := norm_sub_sq_real p z
    change (ell z + (2 * c) * ⟪p, z⟫ ≤ ell p + (2 * c) * ⟪p, p⟫) ∧
      ((ell p + (2 * c) * ⟪p, p⟫ ≤ ell z + (2 * c) * ⟪p, z⟫) → z = p)
    rw [real_inner_self_eq_norm_sq]
    constructor
    · nlinarith [sq_nonneg ‖p - z‖]
    · intro he
      have hsqc := congrArg (fun a : ℝ => c * a) hsq
      have hprod : c * ‖p - z‖ ^ 2 ≤ 0 := by nlinarith only [hcomp, he, hsqc]
      have hsqzero : ‖p - z‖ ^ 2 ≤ 0 := by
        by_contra hn
        have hh := mul_pos hc (lt_of_not_ge hn)
        linarith
      have hzero : ‖p - z‖ = 0 := by nlinarith [norm_nonneg (p - z)]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · have hcomp := hmax hq
    change ell q + c * ‖q‖ ^ 2 ≤ ell p + c * ‖p‖ ^ 2 at hcomp
    nlinarith [sq_nonneg ‖q‖]

lemma closure_convexHull_exposed {K : Set Y} (hK : IsCompact K) (hconv : Convex ℝ K) :
    closure (convexHull ℝ (K.exposedPoints ℝ)) = K := by
  apply (closure_minimal (convexHull_min exposedPoints_subset hconv) hK.isClosed).antisymm
  intro q hq
  by_contra hq'
  obtain ⟨ell, a, ha, haq⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (K.exposedPoints ℝ)).closure isClosed_closure hq'
  obtain ⟨p, hp, happ⟩ := exposed_support_approx hK hq ell (sub_pos.mpr haq)
  have hb := ha p (subset_closure (subset_convexHull ℝ _ hp))
  linarith

/-- Compactness shrinks a slice about its uniquely exposed maximizer. -/
lemma exposed_small_slice {K : Set Y} (hK : IsCompact K) {p : Y}
    (hp : p ∈ K.exposedPoints ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ (ell : Y →L[ℝ] ℝ) (β : ℝ), β < ell p ∧
      ∀ q ∈ K, β < ell q → ‖q - p‖ < r := by
  obtain ⟨hpK, ell, hell⟩ := hp
  let C := K ∩ {q : Y | r ≤ ‖q - p‖}
  have hC : IsCompact C := hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  by_cases hne : C.Nonempty
  · obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne ell.continuous.continuousOn
    have hlt : ell q < ell p := by
      refine lt_of_le_of_ne (hell q hq.1).1 ?_
      intro he
      have hqp := (hell q hq.1).2 he.ge
      have : r ≤ ‖q - p‖ := hq.2
      simp only [hqp, sub_self, norm_zero] at this
      linarith
    refine ⟨ell, ell q, hlt, ?_⟩
    intro z hz hβ
    by_contra hdist
    exact (hmax ⟨hz, le_of_not_gt hdist⟩).not_gt hβ
  · refine ⟨ell, ell p - 1, by linarith, ?_⟩
    intro q hq _
    by_contra hdist
    exact hne ⟨q, hq, le_of_not_gt hdist⟩

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Bourgain's finite-dimensional slice-combination lemma, in the exact form needed for
finite-quotient neighborhoods. Zero weights are harmless and allowed. -/
lemma bourgain_image (T : X →L[ℝ] Y) {u : X} (hu : ‖u‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (ell : ι → X →L[ℝ] ℝ) (β : ι → ℝ),
      (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧
      (∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i y) ∧
      ∀ y : ι → X, (∀ i, ‖y i‖ ≤ 1 ∧ β i < ell i (y i)) →
        ‖T (∑ i, a i • y i) - T u‖ < r := by
  let B := Metric.closedBall (0 : X) 1
  let K := closure (T '' B)
  have hK : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closure, ((Metric.isBounded_closedBall (x := (0 : X)) (r := 1)).image T).closure⟩
  have hconv : Convex ℝ K := ((convex_closedBall (0 : X) 1).linear_image T.toLinearMap).closure
  have hTu : T u ∈ K := subset_closure ⟨u, by simpa [B] using hu, rfl⟩
  rw [← closure_convexHull_exposed hK hconv] at hTu
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hTu (r / 2) (by positivity)
  obtain ⟨ι, hι, a, v, ha, hsum, hv, hpv⟩ := mem_convexHull_iff_exists_fintype.mp hp
  let := hι
  choose ell β hβ hsmall using fun i => exposed_small_slice hK (hv i) (show 0 < r / 2 by positivity)
  have hne : ∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i (T y) := by
    intro i
    have hvi : v i ∈ closure (T '' B) := (hv i).1
    obtain ⟨q, hqβ, y, hy, rfl⟩ := mem_closure_iff.mp hvi {q | β i < ell i q}
      (isOpen_lt continuous_const (ell i).continuous) (hβ i)
    exact ⟨y, by simpa [B] using hy, hqβ⟩
  refine ⟨ι, hι, a, fun i => (ell i).comp T, β, ha, hsum, hne, ?_⟩
  intro y hy
  have hpbound : ‖T (∑ i, a i • y i) - p‖ ≤ r / 2 := by
    have hid : T (∑ i, a i • y i) - p = ∑ i, a i • (T (y i) - v i) := by
      rw [← hpv]
      simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    rw [hid]
    calc
      ‖∑ i, a i • (T (y i) - v i)‖ ≤ ∑ i, ‖a i • (T (y i) - v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, a i * (r / 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)]
        apply mul_le_mul_of_nonneg_left _ (ha i)
        exact (hsmall i (T (y i)) (subset_closure ⟨y i, by simpa [B] using (hy i).1, rfl⟩)
          (hy i).2).le
      _ = r / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hpu : ‖p - T u‖ < r / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hb := norm_add_le (T (∑ i, a i • y i) - p) (p - T u)
  rw [sub_add_sub_cancel] at hb
  linarith

end ExactModuli

end

end OAI
