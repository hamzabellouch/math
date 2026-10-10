import OAI.Geometry.ProjectionVolume.FiniteApproximation
import OAI.Geometry.ProjectionVolume.PolytopeDefinitions

namespace OAI

open Set Metric
open scoped Pointwise RealInnerProductSpace

namespace Paper092

theorem exists_unit_separating_support {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (hne : K.Nonempty) (hv : Convex ℝ K)
    {x : Euclidean n} (hx : x ∉ K) :
    ∃ u : Euclidean n, ‖u‖ = 1 ∧
      SupportGeometry.support K (innerSL ℝ u) < ⟪u, x⟫ := by
  have hx' := (SupportGeometry.mem_iff_inner_le_support hc hne hv).not.mp hx
  push Not at hx'
  obtain ⟨u, hu⟩ := hx'
  have hu0 : u ≠ 0 := by
    intro h
    have hh := (SupportGeometry.le_support hc (innerSL ℝ u) hne.choose_spec).trans_lt hu
    simp [h] at hh
  let v := ‖u‖⁻¹ • u
  have hv1 : ‖v‖ = 1 := by simp [v, norm_smul, hu0]
  obtain ⟨y, hy, hys⟩ := SupportGeometry.exists_support hc hne (innerSL ℝ v)
  refine ⟨v, hv1, ?_⟩
  rw [← hys]
  change ⟪v, y⟫ < ⟪v, x⟫
  simp only [v, real_inner_smul_left]
  exact mul_lt_mul_of_pos_left ((SupportGeometry.le_support hc (innerSL ℝ u) hy).trans_lt hu)
    (inv_pos.mpr (norm_pos_iff.mpr hu0))

theorem unit_support_pos_of_zero_mem_interior {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (h0 : (0 : Euclidean n) ∈ interior K)
    (u : Euclidean n) (hu : ‖u‖ = 1) :
    0 < SupportGeometry.support K (innerSL ℝ u) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hz : (r / 2) • u ∈ K := by
    apply hball
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [abs_of_pos (half_pos hr)]
    linarith
  have hh := SupportGeometry.le_support hc (innerSL ℝ u) hz
  simp only [innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq, hu,
    one_pow, mul_one] at hh
  exact (half_pos hr).trans_le hh

theorem unit_support_le_of_norm_le {n : ℕ} {K : Set (Euclidean n)}
    (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (u : Euclidean n) (hu : ‖u‖ = 1) :
    SupportGeometry.support K (innerSL ℝ u) ≤ R := by
  apply SupportGeometry.support_le hne
  intro x hx
  exact (real_inner_le_norm u x).trans (by simpa [hu] using hR x hx)

theorem norm_le_of_basis_inner_le {n : ℕ} {x : Euclidean n} {R : ℝ}
    (h : ∀ i : Fin n, |⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫| ≤ R) :
    ‖x‖ ≤ n * R := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  calc
    ‖x‖ = ‖∑ i : Fin n, ⟪b i, x⟫ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i : Fin n, ‖⟪b i, x⟫ • b i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |⟪b i, x⟫| := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, R := Finset.sum_le_sum (fun i _ => h i)
    _ = n * R := by simp

theorem subset_interior_smul_of_one_lt {n : ℕ} {K : Set (Euclidean n)}
    (hv : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K)
    {r : ℝ} (hr : 1 < r) : K ⊆ interior (r • K) := by
  have heq : (AffineMap.homothety (0 : Euclidean n) r : Euclidean n → Euclidean n) =
      (fun x => r • x) := by
    funext x
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  change K ⊆ interior ((fun x : Euclidean n => r • x) '' K)
  rw [← heq]
  exact hv.subset_interior_image_homothety_of_one_lt h0 r hr

theorem exists_outer_hpolytope_sandwich {n : ℕ} {K : Set (Euclidean n)}
    (hc : IsCompact K) (hv : Convex ℝ K) (h0 : (0 : Euclidean n) ∈ interior K)
    {r : ℝ} (hr : 1 < r) :
    ∃ (F : Finset (Euclidean n)) (P : HPolytope n {u // u ∈ F}),
      K ⊆ P.body ∧ P.body ⊆ r • K := by
  classical
  have hne : K.Nonempty := ⟨0, interior_subset h0⟩
  obtain ⟨R, hRp, hR⟩ := hc.isBounded.exists_pos_norm_le
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let U := {u : Euclidean n // ‖u‖ = 1}
  let V : U → Set (Euclidean n) := fun u =>
    {x | SupportGeometry.support K (innerSL ℝ u.val) < ⟪u.val, x⟫}
  have hKin := subset_interior_smul_of_one_lt hv h0 hr
  have hcover : closedBall (0 : Euclidean n) (n * R) \ interior (r • K) ⊆ ⋃ u : U, V u := by
    intro x hx
    obtain ⟨u, hu, hsep⟩ := exists_unit_separating_support hc hne hv
      (fun hxK => hx.2 (hKin hxK))
    exact mem_iUnion.mpr ⟨⟨u, hu⟩, hsep⟩
  obtain ⟨t, ht⟩ := ((isCompact_closedBall (0 : Euclidean n) (n * R)).diff
    isOpen_interior).elim_finite_subcover V
      (fun u => isOpen_lt continuous_const (innerSL ℝ u.val).continuous) hcover
  let F := t.image Subtype.val ∪
    (Finset.univ.image b ∪ Finset.univ.image (fun i : Fin n => -b i))
  have htF (u : U) (hu : u ∈ t) : u.val ∈ F :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have hpF (i : Fin n) : b i ∈ F := Finset.mem_union_right _
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hnF (i : Fin n) : -b i ∈ F := Finset.mem_union_right _
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hFunit : ∀ u ∈ F, ‖u‖ = 1 := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      exact v.property
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
        exact b.norm_eq_one i
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
        simp
  let H : Set (Euclidean n) := {x | ∀ u : {u // u ∈ F},
    ⟪u.val, x⟫ ≤ SupportGeometry.support K (innerSL ℝ u.val)}
  have hKH : K ⊆ H := fun x hx u => SupportGeometry.le_support hc (innerSL ℝ u.val) hx
  have hHbound : ∀ x ∈ H, ‖x‖ ≤ n * R := by
    intro x hx
    apply norm_le_of_basis_inner_le
    intro i
    have hp := (hx ⟨b i, hpF i⟩).trans
      (unit_support_le_of_norm_le hne hR (b i) (b.norm_eq_one i))
    have hn := (hx ⟨-b i, hnF i⟩).trans
      (unit_support_le_of_norm_le hne hR (-b i) (by simp))
    apply abs_le.mpr
    refine ⟨?_, hp⟩
    simpa only [inner_neg_left, neg_le] using hn
  have hHr : H ⊆ r • K := by
    intro x hx
    by_contra hxout
    have hxC : x ∈ closedBall (0 : Euclidean n) (n * R) \ interior (r • K) :=
      ⟨by simpa only [mem_closedBall, dist_zero_right] using hHbound x hx,
        fun h => hxout (interior_subset h)⟩
    obtain ⟨u, hut, hux⟩ := mem_iUnion₂.mp (ht hxC)
    exact (not_lt_of_ge (hx ⟨u.val, htF u hut⟩)) hux
  have hHclosed : IsClosed H := by
    dsimp [H]
    rw [ofPred_forall]
    exact isClosed_iInter fun u => isClosed_le (innerSL ℝ u.val).continuous continuous_const
  let P : HPolytope n {u // u ∈ F} := {
    normal := Subtype.val
    offset := fun u => SupportGeometry.support K (innerSL ℝ u.val)
    normal_unit := fun u => hFunit u.val u.property
    compact := (hc.smul r).of_isClosed_subset hHclosed hHr
    strict_feasible := ⟨0, fun u => by
      simpa only [inner_zero_right] using
        unit_support_pos_of_zero_mem_interior hc h0 u.val (hFunit u.val u.property)⟩
    distinct := fun i j hij => Subtype.ext (congrArg Prod.fst hij) }
  exact ⟨F, P, hKH, hHr⟩

end Paper092

end OAI
