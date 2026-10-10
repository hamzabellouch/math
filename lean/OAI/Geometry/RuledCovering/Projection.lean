import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

@[simp] lemma vec2_apply_zero (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] lemma vec2_apply_one (x y : ℝ) : vec2 x y 1 = y := rfl
@[simp] lemma vec3_apply_zero (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] lemma vec3_apply_one (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] lemma vec3_apply_two (x y z : ℝ) : vec3 x y z 2 = z := rfl

lemma inner_vec3 (a b c x y z : ℝ) :
    inner ℝ (vec3 a b c) (vec3 x y z) = a*x+b*y+c*z := by
  simp [vec3, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_succ]
  ring

lemma norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec3]
  ring

/-- The transverse plane in the physical normalization. -/
def planeEmbedding (h : ℝ) : Plane →ₗ[ℝ] Space where
  toFun p := vec3 0 (p 0) (h * p 1)
  map_add' p q := by ext i; fin_cases i <;> simp [vec3, mul_add]
  map_smul' c p := by ext i; fin_cases i <;> simp [vec3, mul_left_comm]

@[simp] lemma planeEmbedding_apply (h : ℝ) (p : Plane) :
    planeEmbedding h p = vec3 0 (p 0) (h * p 1) := rfl

def physicalDirection (h : ℝ) (g : Plane) : Space := vec3 1 (g 0) (h * g 1)

lemma physicalDirection_ne_zero (h : ℝ) (g : Plane) : physicalDirection h g ≠ 0 := by
  intro hz
  have := congrArg (fun x : Space => x 0) hz
  simp [physicalDirection] at this

lemma physicalDirection_norm_sq (h : ℝ) (g : Plane) :
    ‖physicalDirection h g‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 := by
  rw [physicalDirection, norm_vec3_sq]
  ring

lemma physicalDirection_norm_pos (h : ℝ) (g : Plane) : 0 < ‖physicalDirection h g‖ :=
  norm_pos_iff.mpr (physicalDirection_ne_zero h g)

def physicalUnit (h : ℝ) (g : Plane) : Space :=
  ‖physicalDirection h g‖⁻¹ • physicalDirection h g

lemma physicalUnit_norm (h : ℝ) (g : Plane) : ‖physicalUnit h g‖ = 1 := by
  rw [physicalUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (physicalDirection_norm_pos h g).ne']

def rawProjection (h : ℝ) (g : Plane) : Plane →ₗ[ℝ] Space where
  toFun p := planeEmbedding h p -
    (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
      ‖physicalDirection h g‖ ^ 2) • physicalDirection h g
  map_add' p q := by simp only [map_add, inner_add_right, add_div, add_smul]; abel
  map_smul' c p := by
    simp only [map_smul, inner_smul_right, mul_div_assoc, mul_smul, smul_sub, RingHom.id_apply]

lemma rawProjection_mem (h : ℝ) (g p : Plane) :
    rawProjection h g p ∈ ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk, physicalUnit,
    inner_smul_left, RCLike.conj_to_real, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

def perpendicularProjection (h : ℝ) (g : Plane) :
    Plane →ₗ[ℝ] ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) :=
  (rawProjection h g).codRestrict _ (rawProjection_mem h g)

lemma inner_rawProjection (h : ℝ) (g p q : Plane) :
    inner ℝ (rawProjection h g p) (rawProjection h g q) =
      inner ℝ (planeEmbedding h p) (planeEmbedding h q) -
      inner ℝ (physicalDirection h g) (planeEmbedding h p) *
        inner ℝ (physicalDirection h g) (planeEmbedding h q) /
          ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (planeEmbedding h p) (physicalDirection h g)]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

lemma rawProjection_normDet_sq (h : ℝ) (g : Plane) :
    (rawProjection h g).normDet ^ 2 = h ^ 2 / ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  have hd := (rawProjection h g).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
  rw [hd, Matrix.det_fin_two]
  simp only [Matrix.gram_apply, inner_rawProjection, EuclideanSpace.basisFun_apply,
    planeEmbedding_apply, physicalDirection, inner_vec3,
    PiLp.single_apply, Fin.isValue, ↓reduceIte, mul_zero, mul_one,
    one_mul, zero_add]
  simp only [Fin.reduceEq, ↓reduceIte]
  rw [show ‖vec3 1 (g 0) (h * g 1)‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 by
    rw [norm_vec3_sq]; ring]
  have hden : 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma rawProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (rawProjection h g).normDet = h / ‖physicalDirection h g‖ := by
  have hn := physicalDirection_norm_pos h g
  have hs : ((rawProjection h g).normDet * ‖physicalDirection h g‖) ^ 2 = h ^ 2 := by
    rw [mul_pow, rawProjection_normDet_sq, div_mul_cancel₀ _ (pow_ne_zero 2 hn.ne')]
  have hnon := mul_nonneg (rawProjection h g).normDet_nonneg hn.le
  apply (eq_div_iff hn.ne').mpr
  nlinarith

lemma physicalWeight_eq_inv_norm (h : ℝ) (g : Plane) :
    physicalWeight h g = 1 / ‖physicalDirection h g‖ := by
  rw [physicalWeight, ← physicalDirection_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]

lemma perpendicularProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (perpendicularProjection h g).normDet = h * physicalWeight h g := by
  rw [perpendicularProjection, LinearMap.normDet_codRestrict, rawProjection_normDet hh,
    physicalWeight_eq_inv_norm]
  ring

lemma perpendicularPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((Submodule.span ℝ ({u} : Set Space))ᗮ) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

lemma perpendicularProjection_volume {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    volume.real (perpendicularProjection h g '' P) =
      h * physicalWeight h g * volume.real P := by
  have hf := (perpendicularProjection h g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume P
  have hm : (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ Plane) : Measure ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ)) = volume := by
    convert InnerProductSpace.euclideanHausdorffMeasure_eq_volume using 1
    simp only [finrank_euclideanSpace_fin, perpendicularPlane_finrank _ (physicalUnit_norm h g)]
  rw [hm] at hf
  rw [measureReal_def, hf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (perpendicularProjection h g).normDet_nonneg,
    perpendicularProjection_normDet hh]
  rfl

lemma perpendicularProjection_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularProjection h g) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hn
  have hz := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hn
  rw [perpendicularProjection_normDet hh, physicalWeight_eq_inv_norm] at hz
  have hp : 0 < h * (1 / ‖physicalDirection h g‖) :=
    mul_pos hh (one_div_pos.mpr (physicalDirection_norm_pos h g))
  exact hp.ne' hz

lemma IsParallelogram.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsParallelogram P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsParallelogram (f '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨f c, f u, f v, ?_, ?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : (f ∘ ![u, v]) = ![f u, f v] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨c + a • u + b • v, ⟨a, ha, b, hb, rfl⟩, by simp⟩

/-- A genuine cylinder in its perpendicular plane, not an oblique intercept patch. -/
def projectedCylinder (h : ℝ) (g : Plane) (P : Set Plane) : Cylinder where
  axis := physicalUnit h g
  unit_axis := physicalUnit_norm h g
  base := perpendicularProjection h g '' P

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

lemma projectedCylinder_parallelogram {h : ℝ} (hh : 0 < h) (g : Plane)
    {P : Set Plane} (hP : IsParallelogram P) :
    (projectedCylinder h g P).parallelogram :=
  hP.linear_image _ (perpendicularProjection_injective hh g)

lemma projectedCylinder_mem_iff (h : ℝ) (g : Plane) (P : Set Plane) (x : Space) :
    x ∈ (projectedCylinder h g P).carrier ↔
      ∃ p ∈ P, ∃ s : ℝ, x = planeEmbedding h p + s • physicalDirection h g := by
  have hid (p : Plane) (t : ℝ) :
      (perpendicularProjection h g p : Space) + t • physicalUnit h g =
        planeEmbedding h p +
          (t / ‖physicalDirection h g‖ -
            inner ℝ (physicalDirection h g) (planeEmbedding h p) /
              ‖physicalDirection h g‖ ^ 2) • physicalDirection h g := by
    change (planeEmbedding h p -
      (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) • physicalDirection h g) +
      t • (‖physicalDirection h g‖⁻¹ • physicalDirection h g) = _
    simp only [div_eq_mul_inv, smul_smul]
    module
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, t, rfl⟩
    exact ⟨p, hp, _, hid p t⟩
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨perpendicularProjection h g p, ⟨p, hp, rfl⟩,
      (s + inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) * ‖physicalDirection h g‖, ?_⟩
    change planeEmbedding h p + s • physicalDirection h g =
      (perpendicularProjection h g p : Space) + _ • physicalUnit h g
    rw [hid, mul_div_cancel_right₀ _ (physicalDirection_norm_pos h g).ne', add_sub_cancel_right]

lemma projectedCylinder_carrier (h : ℝ) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).carrier = firstPhysicalMap h '' auxiliaryCylinder P g := by
  ext x
  rw [projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨axial s (p + s • g), ⟨s, p, hp, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]
  · rintro ⟨_, ⟨s, p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, s, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]

lemma physicalRuled_mem_projectedCylinder (h : ℝ) (v : Plane → Plane)
    (p g : Plane) (s : ℝ) {P : Set Plane} (hp : p + s • (v p - g) ∈ P) :
    vec3 s (p 0 + s * v p 0) (h * (p 1 + s * v p 1)) ∈
      (projectedCylinder h g P).carrier := by
  rw [projectedCylinder_mem_iff]
  refine ⟨p + s • (v p - g), hp, s, ?_⟩
  ext i
  fin_cases i <;> simp [planeEmbedding, physicalDirection, vec3] <;> ring

end RuledApproximation

end

end OAI
