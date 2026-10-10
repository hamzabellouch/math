import OAI.Geometry.ProjectionVolume.PolytopeDefinitions
import OAI.Geometry.ProjectionVolume.SimplexProjection
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

def slack (x : Euclidean d) (i : ι) : ℝ := P.offset i - ⟪P.normal i, x⟫

def velocity (u : Euclidean d) (i : ι) : ℝ := -⟪P.normal i, u⟫

theorem slack_add_smul (x u : Euclidean d) (t : ℝ) (i : ι) :
    P.slack (x + t • u) i = P.slack x i + t * P.velocity u i := by
  simp only [slack, velocity, inner_add_right, real_inner_smul_right]
  ring

theorem mem_body_iff_slack (x : Euclidean d) :
    x ∈ P.body ↔ ∀ i, 0 ≤ P.slack x i := by
  simp only [body, mem_ofPred_eq, slack, sub_nonneg]

theorem mem_face_iff_slack (i : ι) (x : Euclidean d) :
    x ∈ P.face i ↔ x ∈ P.body ∧ P.slack x i = 0 := by
  change (x ∈ P.body ∧ ⟪P.normal i, x⟫ = P.offset i) ↔ _
  constructor
  · rintro ⟨hx, hi⟩
    exact ⟨hx, by simp [slack, hi]⟩
  · rintro ⟨hx, hi⟩
    exact ⟨hx, (sub_eq_zero.mp hi).symm⟩

theorem body_nonempty : P.body.Nonempty := by
  obtain ⟨x, hx⟩ := P.strict_feasible
  exact ⟨x, fun i => (hx i).le⟩

theorem body_convex : Convex ℝ P.body := by
  intro x hx y hy a b ha hb hab i
  simp only [inner_add_right, real_inner_smul_right]
  calc
    a * ⟪P.normal i, x⟫ + b * ⟪P.normal i, y⟫ ≤
        a * P.offset i + b * P.offset i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = (a + b) * P.offset i := by ring
    _ = P.offset i := by rw [hab, one_mul]

theorem velocity_neg_exists (u : Euclidean d) (hu : u ≠ 0) :
    ∃ i, P.velocity u i < 0 := by
  by_contra! h
  obtain ⟨x, hx, hmax⟩ := P.compact.exists_isMaxOn P.body_nonempty
    (innerSL ℝ u).continuous.continuousOn
  have hx' : x + u ∈ P.body := by
    intro i
    have hi := h i
    dsimp only [velocity] at hi
    simp only [inner_add_right]
    linarith [hx i]
  have hle := hmax hx'
  change ⟪u, x + u⟫ ≤ ⟪u, x⟫ at hle
  rw [inner_add_right] at hle
  have hpos := real_inner_self_pos.mpr hu
  linarith

theorem exists_front_point (x u : Euclidean d) (hu : u ≠ 0)
    (hx : x ∈ P.body) :
    ∃ t : ℝ, 0 ≤ t ∧ x + t • u ∈ P.body ∧
      ∃ i, P.velocity u i < 0 ∧ P.slack (x + t • u) i = 0 := by
  obtain ⟨t, ht, hq, i, hi, hqi⟩ := Paper092.exists_step_to_boundary
    (P.slack x) (P.velocity u) ((P.mem_body_iff_slack x).mp hx)
    (P.velocity_neg_exists u hu)
  refine ⟨t, ht, ?_, i, hi, ?_⟩
  · exact (P.mem_body_iff_slack _).mpr (fun j => by simpa only [slack_add_smul] using hq j)
  · simpa only [slack_add_smul] using hqi

theorem projection_injective_on_front (u x z : Euclidean d)
    (hx : x ∈ P.body) (hz : z ∈ P.body)
    (hxf : ∃ i, P.velocity u i < 0 ∧ P.slack x i = 0)
    (hzf : ∃ i, P.velocity u i < 0 ∧ P.slack z i = 0)
    (hp : (normalHyperplane u).orthogonalProjectionOnto x =
      (normalHyperplane u).orthogonalProjectionOnto z) : x = z := by
  obtain ⟨t, rfl⟩ := (Paper092.projection_eq_iff_parallel u x z).mp hp
  obtain ⟨a, ha, hxa⟩ := hxf
  obtain ⟨b, hb, hzb⟩ := hzf
  rw [slack_add_smul] at hxa
  have ht0 : 0 ≤ t := by
    by_contra ht
    have hprod := mul_pos_of_neg_of_neg (lt_of_not_ge ht) ha
    have hz' := (P.mem_body_iff_slack z).mp hz a
    linarith
  have ht1 : t ≤ 0 := by
    by_contra ht
    have hprod := mul_neg_of_pos_of_neg (lt_of_not_ge ht) hb
    have hxb := (P.mem_body_iff_slack _).mp hx b
    rw [slack_add_smul, hzb] at hxb
    linarith
  simp [le_antisymm ht1 ht0]

theorem projection_eq_front_cover (u : Euclidean d) (hu : u ≠ 0) :
    (normalHyperplane u).orthogonalProjectionOnto '' P.body =
      ⋃ i : {i : ι // P.velocity u i < 0},
        (normalHyperplane u).orthogonalProjectionOnto '' P.face i.val := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, _, hq, i, hi, hqi⟩ := P.exists_front_point x u hu hx
    refine mem_iUnion.mpr ⟨⟨i, hi⟩, x + t • u, ?_, ?_⟩
    · exact (P.mem_face_iff_slack _ _).mpr ⟨hq, hqi⟩
    · exact (Paper092.projection_eq_iff_parallel u (x + t • u) x).mpr ⟨t, rfl⟩
  · intro hy
    obtain ⟨i, x, hx, hpx⟩ := mem_iUnion.mp hy
    exact ⟨x, hx.1, hpx⟩

theorem front_faces_projection_inter_eq (u : Euclidean d) (a b : ι)
    (ha : P.velocity u a < 0) (hb : P.velocity u b < 0) :
    ((normalHyperplane u).orthogonalProjectionOnto '' P.face a) ∩
      ((normalHyperplane u).orthogonalProjectionOnto '' P.face b) =
        (normalHyperplane u).orthogonalProjectionOnto '' (P.face a ∩ P.face b) := by
  apply le_antisymm
  · rintro y ⟨⟨x, hx, hpx⟩, ⟨z, hz, hpz⟩⟩
    have hxa := (P.mem_face_iff_slack _ _).mp hx
    have hzb := (P.mem_face_iff_slack _ _).mp hz
    have heq : x = z := P.projection_injective_on_front u x z hxa.1 hzb.1
      ⟨a, ha, hxa.2⟩ ⟨b, hb, hzb.2⟩ (hpx.trans hpz.symm)
    subst z
    exact ⟨x, ⟨hx, hz⟩, hpx⟩
  · exact image_inter_subset _ _ _

def slackAffine (i : ι) : Euclidean d →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (Euclidean d) (P.offset i) - (innerₛₗ ℝ (P.normal i)).toAffineMap

theorem slackAffine_apply (i : ι) (x : Euclidean d) : P.slackAffine i x = P.slack x i := rfl

theorem seam_projection_invariant (u x : Euclidean d) (a b : ι) :
    P.velocity u b * P.slack ((normalHyperplane u).orthogonalProjectionOnto x) a -
      P.velocity u a * P.slack ((normalHyperplane u).orthogonalProjectionOnto x) b =
        P.velocity u b * P.slack x a - P.velocity u a * P.slack x b := by
  obtain ⟨t, ht⟩ := (Paper092.projection_eq_iff_parallel u x
    ((normalHyperplane u).orthogonalProjectionOnto x)).mp
      ((normalHyperplane u).orthogonalProjectionOnto_mem_subspace_eq_self
        ((normalHyperplane u).orthogonalProjectionOnto x)).symm
  conv_rhs => rw [ht, slack_add_smul, slack_add_smul]
  ring

private theorem index_eq_of_weighted_slack_zero (a b : ι) (r s : ℝ)
    (hr : r < 0) (hs : s < 0)
    (h : ∀ x, r * P.slack x a - s * P.slack x b = 0) : a = b := by
  have h0 := h 0
  simp only [slack, inner_zero_right, sub_zero] at h0
  have hn : r • P.normal a = s • P.normal b := by
    apply ext_inner_right ℝ
    intro x
    simp only [real_inner_smul_left]
    have hx := h x
    dsimp only [slack] at hx
    nlinarith
  have hnorm := congrArg norm hn
  simp only [norm_smul, Real.norm_eq_abs, P.normal_unit, mul_one,
    abs_of_neg hr, abs_of_neg hs] at hnorm
  have hrs : r = s := by linarith
  rw [hrs] at hn h0
  have hn' : P.normal a = P.normal b :=
    smul_right_injective (Euclidean d) (ne_of_lt hs) hn
  have hc : P.offset a = P.offset b :=
    mul_left_cancel₀ (ne_of_lt hs) (sub_eq_zero.mp h0)
  exact P.distinct (Prod.ext hn' hc)

theorem projected_seam_null (u : Euclidean d) (a b : ι) (hab : a ≠ b)
    (ha : P.velocity u a < 0) (hb : P.velocity u b < 0) :
    volume {y : normalHyperplane u |
      P.velocity u b * P.slack y.val a - P.velocity u a * P.slack y.val b = 0} = 0 := by
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
    apply hab
    apply P.index_eq_of_weighted_slack_zero a b (P.velocity u b) (P.velocity u a) hb ha
    intro x
    have hy : (normalHyperplane u).orthogonalProjectionOnto x ∈ S := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ _ _
    have hz := (hmem _).mp hy
    rwa [seam_projection_invariant] at hz
  have hset : {y : normalHyperplane u |
      P.velocity u b * P.slack y.val a - P.velocity u a * P.slack y.val b = 0} = S := by
    ext y
    exact (hmem y).symm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem projected_front_faces_aedisjoint (u : Euclidean d) (a b : ι) (hab : a ≠ b)
    (ha : P.velocity u a < 0) (hb : P.velocity u b < 0) :
    AEDisjoint volume
      ((normalHyperplane u).orthogonalProjectionOnto '' P.face a)
      ((normalHyperplane u).orthogonalProjectionOnto '' P.face b) := by
  rw [AEDisjoint, P.front_faces_projection_inter_eq u a b ha hb]
  apply measure_mono_null _ (P.projected_seam_null u a b hab ha hb)
  rintro y ⟨x, hx, rfl⟩
  change P.velocity u b * P.slack ((normalHyperplane u).orthogonalProjectionOnto x) a -
    P.velocity u a * P.slack ((normalHyperplane u).orthogonalProjectionOnto x) b = 0
  rw [seam_projection_invariant,
    ((P.mem_face_iff_slack a x).mp hx.1).2, ((P.mem_face_iff_slack b x).mp hx.2).2]
  simp

theorem face_isCompact (i : ι) : IsCompact (P.face i) :=
  P.compact.inter_right (isClosed_eq (innerSL ℝ (P.normal i)).continuous continuous_const)

theorem projected_face_isCompact (u : Euclidean d) (i : ι) :
    IsCompact ((normalHyperplane u).orthogonalProjectionOnto '' P.face i) :=
  (P.face_isCompact i).image (normalHyperplane u).orthogonalProjectionOnto.continuous

theorem projectionVolume_eq_front_sum (u : Euclidean d) (hu : u ≠ 0) :
    projectionVolume P.body u =
      ∑ i : {i : ι // P.velocity u i < 0},
        volume ((normalHyperplane u).orthogonalProjectionOnto '' P.face i.val) := by
  classical
  unfold projectionVolume
  rw [P.projection_eq_front_cover u hu]
  have hd : Pairwise (fun a b : {i : ι // P.velocity u i < 0} =>
      AEDisjoint volume
        ((normalHyperplane u).orthogonalProjectionOnto '' P.face a.val)
        ((normalHyperplane u).orthogonalProjectionOnto '' P.face b.val)) := by
    intro a b hab
    exact P.projected_front_faces_aedisjoint u a.val b.val (Subtype.coe_injective.ne hab)
      a.property b.property
  rw [measure_iUnion₀ hd (fun i =>
    (P.projected_face_isCompact u i.val).measurableSet.nullMeasurableSet)]
  exact tsum_fintype _

theorem brightness_eq_front_sum (u : Euclidean d) (hu : u ≠ 0) :
    brightness P.body u =
      ∑ i : {i : ι // P.velocity u i < 0}, brightness (P.face i.val) u := by
  classical
  simp only [brightness]
  rw [P.projectionVolume_eq_front_sum u hu, ENNReal.toReal_sum]
  · exact Finset.mul_sum _ _ _
  · intro i _
    exact (P.projected_face_isCompact u i.val).measure_lt_top.ne

theorem face_brightness (i : ι) (u : Euclidean d) :
    brightness (P.face i) u = P.faceArea i * |⟪u, P.normal i⟫| := by
  have h := Paper092.brightness_of_subset_affine_hyperplane u (P.normal i)
    (P.normal_unit i) (P.offset i) (P.face i) (fun _ hx => hx.2)
  simpa only [faceArea, mul_comm] using h

end Paper092.HPolytope

end

end OAI
