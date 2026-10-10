import OAI.Geometry.ProjectionVolume.PolytopeFacets
import OAI.Geometry.ProjectionVolume.CubeFibers
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem projectionVolume_le_surface (S : Set (Euclidean d)) (u : Euclidean d) (hu : u ≠ 0) :
    projectionVolume S u ≤ μHE[d - 1] S := by
  unfold projectionVolume
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    normalHyperplane_finrank u hu]
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  exact mul_le_mul_right
    (hausdorffMeasure_orthogonalProjectionOnto_le (normalHyperplane u)
      ((d - 1 : ℕ) : ℝ) S (by positivity)) _

theorem projected_face_inter_null (u : Euclidean d) (hu : u ≠ 0) (a b : ι) (hab : a ≠ b) :
    volume ((normalHyperplane u).orthogonalProjectionOnto '' (P.face a ∩ P.face b)) = 0 := by
  apply le_antisymm _ bot_le
  exact (projectionVolume_le_surface (P.face a ∩ P.face b) u hu).trans_eq
    (P.face_inter_surface_null a b hab)

theorem strict_face_point_mem_intrinsicInterior (a : ι) (x : Euclidean d)
    (hx : x ∈ P.face a) (hstrict : ∀ b, b ≠ a → ⟪P.normal b, x⟫ < P.offset b) :
    x ∈ intrinsicInterior ℝ (P.face a) := by
  classical
  let Q := affineSpan ℝ (P.face a)
  let T : AffineSubspace ℝ (Euclidean d) :=
    (affineSpan ℝ ({P.offset a} : Set ℝ)).comap (innerₛₗ ℝ (P.normal a)).toAffineMap
  have hQle : Q ≤ T := by
    apply affineSpan_le.mpr
    intro y hy
    simpa [T] using hy.2
  have hplane (y : Q) : ⟪P.normal a, (y : Euclidean d)⟫ = P.offset a := by
    have h := hQle y.property
    simpa [T] using h
  let S : Set Q := ⋂ b : {b : ι // b ≠ a},
    {y | ⟪P.normal b.val, (y : Euclidean d)⟫ < P.offset b.val}
  have hopen : IsOpen S := isOpen_iInter_of_finite fun b =>
    isOpen_lt ((innerSL ℝ (P.normal b.val)).continuous.comp continuous_subtype_val) continuous_const
  let xQ : Q := ⟨x, subset_affineSpan ℝ _ hx⟩
  have hxS : xQ ∈ S := mem_iInter.mpr (fun b => hstrict b.val b.property)
  have hsub : S ⊆ (Subtype.val ⁻¹' P.face a : Set Q) := by
    intro y hy
    refine ⟨?_, hplane y⟩
    intro b
    by_cases hba : b = a
    · simpa only [hba, hplane y] using le_refl (P.offset a)
    · exact (mem_iInter.mp hy ⟨b, hba⟩).le
  apply mem_intrinsicInterior.mpr
  refine ⟨xQ, interior_mono hsub ?_, rfl⟩
  simpa only [hopen.interior_eq] using hxS

def badProjection (u : Euclidean d) : Set (normalHyperplane u) :=
  ⋃ a : ι, ⋃ b : {b : ι // b ≠ a},
    (normalHyperplane u).orthogonalProjectionOnto '' (P.face a ∩ P.face b.val)

theorem badProjection_null (u : Euclidean d) (hu : u ≠ 0) : volume (P.badProjection u) = 0 := by
  apply measure_iUnion_null
  intro a
  apply measure_iUnion_null
  intro b
  exact P.projected_face_inter_null u hu a b.val (Ne.symm b.property)

theorem strict_of_not_badProjection (u : Euclidean d) (y : normalHyperplane u)
    (hy : y ∉ P.badProjection u) (a : ι) (x : Euclidean d) (hx : x ∈ P.face a)
    (hproj : (normalHyperplane u).orthogonalProjectionOnto x = y) :
    ∀ b, b ≠ a → ⟪P.normal b, x⟫ < P.offset b := by
  intro b hba
  apply lt_of_le_of_ne (hx.1 b)
  intro hbx
  apply hy
  exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨⟨b, hba⟩, x, ⟨hx, hx.1, hbx⟩, hproj⟩⟩

theorem affineSpan_face_of_not_badProjection (u : Euclidean d)
    (y : normalHyperplane u) (hy : y ∉ P.badProjection u) (a : ι)
    (ha : y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face a) :
    (affineSpan ℝ (P.face a) : Set (Euclidean d)) =
      {x | ⟪P.normal a, x⟫ = P.offset a} := by
  obtain ⟨x, hx, hxy⟩ := ha
  apply P.affineSpan_face_of_essential a
  intro hred
  obtain ⟨b, hba, hb⟩ := P.exists_other_active_of_redundant a hred x hx
  exact (ne_of_lt (P.strict_of_not_badProjection u y hy a x hx hxy b hba)) hb

theorem parameter_of_projection_eq (u : Euclidean d) (y : normalHyperplane u)
    (x : Euclidean d) (hx : (normalHyperplane u).orthogonalProjectionOnto x = y) :
    ∃ t : ℝ, x = (y : Euclidean d) + t • u := by
  apply (Paper092.projection_eq_iff_parallel u x y).mp
  exact hx.trans ((normalHyperplane u).orthogonalProjectionOnto_mem_subspace_eq_self y).symm

theorem interval_of_opposite_faces (u y : Euclidean d) (a b : ι) (l r : ℝ)
    (hla : y + l • u ∈ P.face a) (hrb : y + r • u ∈ P.face b)
    (ha : 0 < P.velocity u a) (hb : P.velocity u b < 0) :
    lineFiber P.body y u = Icc l r := by
  have hl := (P.mem_face_iff_slack a _).mp hla
  have hr := (P.mem_face_iff_slack b _).mp hrb
  rw [P.slack_add_smul] at hl hr
  ext t
  change y + t • u ∈ P.body ↔ l ≤ t ∧ t ≤ r
  constructor
  · intro ht
    have hta := (P.mem_body_iff_slack _).mp ht a
    have htb := (P.mem_body_iff_slack _).mp ht b
    rw [P.slack_add_smul] at hta htb
    constructor <;> nlinarith
  · rintro ⟨hlt, htr⟩
    apply (P.mem_body_iff_slack _).mpr
    intro i
    rw [P.slack_add_smul]
    by_cases hi : 0 ≤ P.velocity u i
    · have hli := (P.mem_body_iff_slack _).mp hl.1 i
      rw [P.slack_add_smul] at hli
      nlinarith [mul_nonneg (sub_nonneg.mpr hlt) hi]
    · have hri := (P.mem_body_iff_slack _).mp hr.1 i
      rw [P.slack_add_smul] at hri
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htr) (le_of_not_ge hi)]

theorem two_facet_interiors_outside_bad (u : Euclidean d) (hu : u ≠ 0)
    (y : normalHyperplane u) (hy : y ∉ P.badProjection u)
    (hyP : y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.body) :
    ∃ (a b : ι) (l r : ℝ), a ≠ b ∧ l < r ∧
      lineFiber P.body (y : Euclidean d) u = Icc l r ∧
      (y : Euclidean d) + l • u ∈ intrinsicInterior ℝ (P.face a) ∧
      (y : Euclidean d) + r • u ∈ intrinsicInterior ℝ (P.face b) ∧
      {i | y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face i} = {a, b} ∧
      {i | y ∈ (normalHyperplane u).orthogonalProjectionOnto ''
        intrinsicInterior ℝ (P.face i)} = {a, b} := by
  classical
  obtain ⟨p, hp, hpy⟩ := hyP
  obtain ⟨tf, _, hpf, b, hb, hqf⟩ := P.exists_front_point p u hu hp
  have hf : p + tf • u ∈ P.face b := (P.mem_face_iff_slack _ _).mpr ⟨hpf, hqf⟩
  have hfp : (normalHyperplane u).orthogonalProjectionOnto (p + tf • u) = y :=
    ((Paper092.projection_eq_iff_parallel u (p + tf • u) p).mpr ⟨tf, rfl⟩).trans hpy
  obtain ⟨r, hrf⟩ := parameter_of_projection_eq u y (p + tf • u) hfp
  have hrb : (y : Euclidean d) + r • u ∈ P.face b := by rwa [hrf] at hf
  have hrp : (normalHyperplane u).orthogonalProjectionOnto ((y : Euclidean d) + r • u) = y := by
    rwa [hrf] at hfp
  obtain ⟨tb, _, hpb, a, ha', hqb⟩ := P.exists_front_point p (-u) (neg_ne_zero.mpr hu) hp
  have ha : 0 < P.velocity u a := by simpa only [velocity_neg, neg_lt_zero] using ha'
  have hback : p + tb • (-u) ∈ P.face a := (P.mem_face_iff_slack _ _).mpr ⟨hpb, hqb⟩
  have hbp : (normalHyperplane u).orthogonalProjectionOnto (p + tb • (-u)) = y := by
    have heq : p + tb • (-u) = p + (-tb) • u := by simp
    rw [heq]
    exact ((Paper092.projection_eq_iff_parallel u (p + (-tb) • u) p).mpr ⟨-tb, rfl⟩).trans hpy
  obtain ⟨l, hlb⟩ := parameter_of_projection_eq u y (p + tb • (-u)) hbp
  have hla : (y : Euclidean d) + l • u ∈ P.face a := by rwa [hlb] at hback
  have hlp : (normalHyperplane u).orthogonalProjectionOnto ((y : Euclidean d) + l • u) = y := by
    rwa [hlb] at hbp
  have hab : a ≠ b := by intro h; subst b; linarith
  have hls := P.strict_of_not_badProjection u y hy a _ hla hlp
  have hrs := P.strict_of_not_badProjection u y hy b _ hrb hrp
  have hlr : l < r := by
    have hpos : 0 < P.slack ((y : Euclidean d) + l • u) b := sub_pos.mpr (hls b hab.symm)
    have hzero := ((P.mem_face_iff_slack b _).mp hrb).2
    rw [P.slack_add_smul] at hpos hzero
    by_contra h
    have hprod := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_gt h)) hb.le
    nlinarith
  have hint := P.interval_of_opposite_faces u y a b l r hla hrb ha hb
  have hli := P.strict_face_point_mem_intrinsicInterior a _ hla hls
  have hri := P.strict_face_point_mem_intrinsicInterior b _ hrb hrs
  have hfaces : {i | y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face i} = {a, b} := by
    ext i
    change (y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face i) ↔ i = a ∨ i = b
    constructor
    · rintro ⟨z, hz, hzy⟩
      by_cases hia : i = a
      · exact Or.inl hia
      by_cases hib : i = b
      · exact Or.inr hib
      exfalso
      obtain ⟨t, hzt⟩ := parameter_of_projection_eq u y z hzy
      have ht : t ∈ Icc l r := by
        rw [← hint]
        change (y : Euclidean d) + t • u ∈ P.body
        rw [← hzt]
        exact hz.1
      have hzero : P.slack ((y : Euclidean d) + t • u) i = 0 := by
        rw [← hzt]
        exact ((P.mem_face_iff_slack i z).mp hz).2
      have hlpos : 0 < P.slack ((y : Euclidean d) + l • u) i := sub_pos.mpr (hls i hia)
      have hrpos : 0 < P.slack ((y : Euclidean d) + r • u) i := sub_pos.mpr (hrs i hib)
      rw [P.slack_add_smul] at hzero hlpos hrpos
      by_cases hi : 0 ≤ P.velocity u i
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) hi]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (le_of_not_ge hi)]
    · rintro (rfl | rfl)
      · exact ⟨_, hla, hlp⟩
      · exact ⟨_, hrb, hrp⟩
  refine ⟨a, b, l, r, hab, hlr, hint, hli, hri, hfaces, ?_⟩
  ext i
  change (y ∈ (normalHyperplane u).orthogonalProjectionOnto '' intrinsicInterior ℝ (P.face i)) ↔
    i = a ∨ i = b
  constructor
  · intro hi
    have hiface : y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face i :=
      Set.image_mono intrinsicInterior_subset hi
    have hm : i ∈ ({a, b} : Set ι) := hfaces ▸ hiface
    simpa only [mem_insert_iff, mem_singleton_iff] using hm
  · rintro (rfl | rfl)
    · exact ⟨_, hli, hlp⟩
    · exact ⟨_, hri, hrp⟩

theorem ae_two_facet_interiors (u : Euclidean d) (hu : u ≠ 0) :
    ∀ᵐ y : normalHyperplane u ∂volume,
      y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.body →
      ∃ (a b : ι) (l r : ℝ), a ≠ b ∧ l < r ∧
        lineFiber P.body (y : Euclidean d) u = Icc l r ∧
        (y : Euclidean d) + l • u ∈ intrinsicInterior ℝ (P.face a) ∧
        (y : Euclidean d) + r • u ∈ intrinsicInterior ℝ (P.face b) ∧
        {i | y ∈ (normalHyperplane u).orthogonalProjectionOnto '' P.face i} = {a, b} ∧
        {i | y ∈ (normalHyperplane u).orthogonalProjectionOnto ''
          intrinsicInterior ℝ (P.face i)} = {a, b} := by
  have hgood : ∀ᵐ y : normalHyperplane u ∂volume, y ∉ P.badProjection u := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using P.badProjection_null u hu
  filter_upwards [hgood] with y hy
  exact P.two_facet_interiors_outside_bad u hu y hy

end Paper092.HPolytope

end

end OAI
