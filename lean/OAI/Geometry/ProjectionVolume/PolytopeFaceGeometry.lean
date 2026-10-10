import OAI.Geometry.ProjectionVolume.PolytopeCauchy

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem projected_seam_null_left (u : Euclidean d) (a b : ι) (hab : a ≠ b)
    (ha : P.velocity u a < 0) :
    volume {y : normalHyperplane u |
      P.velocity u b * P.slack y.val a - P.velocity u a * P.slack y.val b = 0} = 0 := by
  by_cases hb : P.velocity u b < 0
  · exact P.projected_seam_null u a b hab ha hb
  let f : normalHyperplane u →ᵃ[ℝ] ℝ :=
    P.velocity u b • ((P.slackAffine a).comp (normalHyperplane u).subtype.toAffineMap) -
    P.velocity u a • ((P.slackAffine b).comp (normalHyperplane u).subtype.toAffineMap)
  let S : AffineSubspace ℝ (normalHyperplane u) :=
    (affineSpan ℝ ({0} : Set ℝ)).comap f
  have hmem (y : normalHyperplane u) : y ∈ S ↔
      P.velocity u b * P.slack y.val a - P.velocity u a * P.slack y.val b = 0 := by
    simp [S, f, slackAffine_apply, smul_eq_mul]
  have hproper : S ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := P.strict_feasible
    have hq : ∀ i, 0 < P.slack x i := fun i => sub_pos.mpr (hx i)
    have hy : (normalHyperplane u).orthogonalProjectionOnto x ∈ S := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ _ _
    have hz := (hmem _).mp hy
    rw [seam_projection_invariant] at hz
    have hpos := mul_nonneg (le_of_not_gt hb) (hq a).le
    have hneg := mul_neg_of_neg_of_pos ha (hq b)
    linarith
  have hset : {y : normalHyperplane u |
      P.velocity u b * P.slack y.val a - P.velocity u a * P.slack y.val b = 0} = S := by
    ext y
    exact (hmem y).symm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem face_inter_surface_null (a b : ι) (hab : a ≠ b) :
    μHE[d - 1] (P.face a ∩ P.face b) = 0 := by
  have ha : P.velocity (P.normal a) a < 0 := by
    simp [velocity, P.normal_unit]
  have hp : projectionVolume (P.face a ∩ P.face b) (P.normal a) = 0 := by
    unfold projectionVolume
    apply measure_mono_null _ (P.projected_seam_null_left (P.normal a) a b hab ha)
    rintro y ⟨x, hx, rfl⟩
    change P.velocity (P.normal a) b *
        P.slack ((normalHyperplane (P.normal a)).orthogonalProjectionOnto x) a -
      P.velocity (P.normal a) a *
        P.slack ((normalHyperplane (P.normal a)).orthogonalProjectionOnto x) b = 0
    rw [seam_projection_invariant, ((P.mem_face_iff_slack a x).mp hx.1).2,
      ((P.mem_face_iff_slack b x).mp hx.2).2]
    simp
  have hv := Paper092.projectionVolume_of_subset_affine_hyperplane
    (P.normal a) (P.normal a) (P.normal_unit a) (P.normal_unit a)
    (P.offset a) (P.face a ∩ P.face b) (fun _ hx => hx.1.2)
  simp only [real_inner_self_eq_norm_sq, P.normal_unit, one_pow, abs_one,
    ENNReal.ofReal_one, one_mul] at hv
  exact hv.symm.trans hp

theorem exists_other_active_of_redundant (i : ι)
    (hred : ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i)
    (x : Euclidean d) (hx : x ∈ P.face i) :
    ∃ j, j ≠ i ∧ ⟪P.normal j, x⟫ = P.offset j := by
  classical
  by_contra! hn
  let S : Set (Euclidean d) := ⋂ j : {j : ι // j ≠ i},
    {y | ⟪P.normal j.val, y⟫ < P.offset j.val}
  have hopen : IsOpen S := isOpen_iInter_of_finite fun j =>
    isOpen_lt (innerSL ℝ (P.normal j.val)).continuous continuous_const
  have hxS : x ∈ S := by
    apply mem_iInter.mpr
    intro j
    exact lt_of_le_of_ne (hx.1 j.val) (hn j.val j.property)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxS
  have hyball : x + (ε / 2) • P.normal i ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, P.normal_unit,
      mul_one, abs_of_pos (div_pos hε (by norm_num : (0 : ℝ) < 2))]
    linarith
  have hyS := hball hyball
  have hy := hred (x + (ε / 2) • P.normal i) (fun j hji =>
    (mem_iInter.mp hyS ⟨j, hji⟩).le)
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    P.normal_unit, one_pow, mul_one, hx.2] at hy
  linarith

theorem redundant_face_surface_null (i : ι)
    (hred : ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    μHE[d - 1] (P.face i) = 0 := by
  classical
  apply measure_mono_null (t := ⋃ j : {j : ι // j ≠ i}, P.face i ∩ P.face j.val)
  · intro x hx
    obtain ⟨j, hji, hj⟩ := P.exists_other_active_of_redundant i hred x hx
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, hx, hx.1, hj⟩
  · apply measure_iUnion_null
    intro j
    exact P.face_inter_surface_null i j.val (Ne.symm j.property)

theorem redundant_faceArea_zero (i : ι)
    (hred : ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    P.faceArea i = 0 := by
  rw [faceArea, P.redundant_face_surface_null i hred, ENNReal.toReal_zero]

theorem exists_strict_face_point_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    ∃ x ∈ P.face i, ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
  classical
  push Not at hessential
  obtain ⟨y, hy, hyi⟩ := hessential
  obtain ⟨z, hz⟩ := P.strict_feasible
  have hden : 0 < ⟪P.normal i, y⟫ - ⟪P.normal i, z⟫ := by linarith [hz i]
  let t : ℝ := (P.offset i - ⟪P.normal i, z⟫) /
    (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫)
  have ht0 : 0 < t := div_pos (sub_pos.mpr (hz i)) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have htmul : t * (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫) =
      P.offset i - ⟪P.normal i, z⟫ := div_mul_cancel₀ _ hden.ne'
  let x := (1 - t) • z + t • y
  have hxi : ⟪P.normal i, x⟫ = P.offset i := by
    dsimp [x]
    simp only [inner_add_right, real_inner_smul_right]
    nlinarith
  have hxj : ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
    intro j hji
    have hleft := mul_lt_mul_of_pos_left (hz j) (sub_pos.mpr ht1)
    have hright := mul_le_mul_of_nonneg_left (hy j hji) ht0.le
    dsimp [x]
    simp only [inner_add_right, real_inner_smul_right]
    nlinarith
  refine ⟨x, ⟨?_, hxi⟩, hxj⟩
  intro j
  by_cases hji : j = i
  · simpa only [hji, hxi] using le_refl (P.offset i)
  · exact (hxj j hji).le

end Paper092.HPolytope

end

end OAI
