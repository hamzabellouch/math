import OAI.Geometry.CylinderCovering.Beams.StripDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace CylinderCovering.BeamStrip

lemma denominator_pos (q : ℝ) : 0 < denominator q := by
  unfold denominator
  positivity

lemma denominator_sq (q : ℝ) : denominator q ^ 2 = 2 * (1 + q ^ 2) := by
  unfold denominator
  rw [Real.sq_sqrt]
  positivity

lemma inner_vec (a b c x y z : ℝ) :
    inner ℝ (vec a b c) (vec x y z) = a*x+b*y+c*z := by
  simp [vec, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_succ]
  ring

lemma norm_vec_sq (a b c : ℝ) : ‖vec a b c‖ ^ 2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]
  ring

lemma normal_norm (q : ℝ) : ‖normal q‖ = 1 := by
  have hd := denominator_sq q
  have hn := denominator_pos q
  have hs : ‖normal q‖ ^ 2 = 1 := by
    rw [normal, norm_vec_sq]
    field_simp [hn.ne']
    nlinarith
  nlinarith [norm_nonneg (normal q)]

lemma axis_norm (q : ℝ) : ‖axis q‖ = 1 := by
  have hd := denominator_sq q
  have hn := denominator_pos q
  have hs : ‖axis q‖ ^ 2 = 1 := by
    rw [axis, norm_vec_sq]
    field_simp [hn.ne']
    nlinarith
  nlinarith [norm_nonneg (axis q)]

lemma normal_axis_inner (q : ℝ) : inner ℝ (normal q) (axis q) = 0 := by
  rw [normal, axis, inner_vec]
  ring

lemma axis_vertical_inner (q : ℝ) : inner ℝ (axis q) vertical = 0 := by
  rw [axis, vertical, inner_vec]
  ring

lemma normal_vertical_inner (q : ℝ) : inner ℝ (normal q) vertical = 0 := by
  rw [normal, vertical, inner_vec]
  ring

lemma vertical_norm : ‖vertical‖ = 1 := by
  have hs : ‖vertical‖ ^ 2 = 1 := by rw [vertical, norm_vec_sq]; norm_num
  nlinarith [norm_nonneg vertical]

lemma rectangle_perpendicular (q A l r : ℝ) :
    ∀ z ∈ rectangle q A l r, inner ℝ (axis q) z = 0 := by
  rintro z ⟨s, hs, t, ht, rfl⟩
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    ← real_inner_comm (axis q) (normal q), normal_axis_inner, axis_vertical_inner]
  ring

lemma rectangle_compact (q A l r : ℝ) : IsCompact (rectangle q A l r) := by
  have heq : rectangle q A l r =
      (fun p : ℝ × ℝ => p.1 • normal q + p.2 • vertical) '' (Icc (-A) A ×ˢ Icc l r) := by
    ext z
    simp only [rectangle, mem_ofPred_eq, mem_image, mem_prod]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
    · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
      exact ⟨s,hs,t,ht,rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

lemma IsHorizontalRectangle.isCompact {C : RuledApproximation.Cylinder}
    (hC : IsHorizontalRectangle C) : IsCompact C.base := by
  obtain ⟨q,A,l,r,hA,hlr,haxis,hbase⟩ := hC
  rw [Subtype.isCompact_iff,hbase]
  exact rectangle_compact q A l r

lemma IsHorizontalRectangle.measurableSet {C : RuledApproximation.Cylinder}
    (hC : IsHorizontalRectangle C) : MeasurableSet C.base := hC.isCompact.measurableSet

lemma IsHorizontalRectangle.finite_volume {C : RuledApproximation.Cylinder}
    (hC : IsHorizontalRectangle C) : volume C.base ≠ ⊤ := hC.isCompact.measure_lt_top.ne

def frameLinear (q : ℝ) : Plane →ₗ[ℝ] Space where
  toFun p := p 0 • normal q + p 1 • vertical
  map_add' p r := by simp only [PiLp.add_apply, add_smul]; module
  map_smul' c p := by simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul]; module

lemma frame_inner (q : ℝ) (p r : Plane) :
    inner ℝ (frameLinear q p) (frameLinear q r) = inner ℝ p r := by
  have hvn : inner ℝ vertical (normal q) = 0 := by
    rw [vertical, normal, inner_vec]
    ring
  simp only [frameLinear, LinearMap.coe_mk, AddHom.coe_mk,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq, normal_norm, vertical_norm,
    normal_vertical_inner, hvn]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

def frame (q : ℝ) : Plane →ₗᵢ[ℝ] Space :=
  (frameLinear q).isometryOfInner (frame_inner q)

def coordinateBox (A l r : ℝ) : Set (Fin 2 → ℝ) :=
  Icc ![-A, l] ![A, r]

def planeBox (A l r : ℝ) : Set Plane := WithLp.toLp 2 '' coordinateBox A l r

lemma rectangle_image (q A l r : ℝ) :
    rectangle q A l r = frame q '' planeBox A l r := by
  ext z
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨WithLp.toLp 2 ![s,t], ?_, rfl⟩
    refine ⟨![s,t], ?_, rfl⟩
    constructor <;> intro i <;> fin_cases i <;> simp_all
  · rintro ⟨p, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, ⟨hv.1 0,hv.2 0⟩,v 1,⟨hv.1 1,hv.2 1⟩,rfl⟩

lemma planeBox_volume {A l r : ℝ} (hA : 0 ≤ A) (hlr : l ≤ r) :
    volume.real (planeBox A l r) = 2*A*(r-l) := by
  have heq : planeBox A l r = WithLp.ofLp ⁻¹' coordinateBox A l r := by
    ext p
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hp
      exact ⟨WithLp.ofLp p,hp,rfl⟩
  have hv : volume (planeBox A l r) = volume (coordinateBox A l r) := by
    rw [heq]
    exact (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage (measurableSet_Icc.nullMeasurableSet)
  have hab : ![-A,l] ≤ ![A,r] := by
    intro i
    fin_cases i <;> simp <;> linarith
  rw [measureReal_def, hv, coordinateBox, Real.volume_Icc_pi_toReal hab]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one ]
  ring

lemma rectangle_area {q A l r : ℝ} (hA : 0 ≤ A) (hlr : l ≤ r) :
    area (rectangle q A l r) = 2*A*(r-l) := by
  have hm := (frame q).toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (planeBox A l r)
  simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
    ENNReal.ofReal_one, one_mul] at hm
  rw [area, rectangle_image]
  change (Measure.euclideanHausdorffMeasure 2 ((frame q).toLinearMap '' planeBox A l r)).toReal = _
  rw [hm]
  exact planeBox_volume hA hlr

lemma frame_mem_perpendicular (q : ℝ) (p : Plane) :
    frame q p ∈ ((Submodule.span ℝ ({axis q} : Set Space))ᗮ) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  change inner ℝ (axis q) (p 0 • normal q + p 1 • vertical) = 0
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    ← real_inner_comm (axis q) (normal q), normal_axis_inner, axis_vertical_inner]
  ring

def perpendicularFrame (q : ℝ) :
    Plane →ₗᵢ[ℝ] ((Submodule.span ℝ ({axis q} : Set Space))ᗮ) where
  toLinearMap := (frame q).toLinearMap.codRestrict _ (frame_mem_perpendicular q)
  norm_map' p := (frame q).norm_map p

def rectangleCylinder (q A l r : ℝ) : RuledApproximation.Cylinder where
  axis := axis q
  unit_axis := axis_norm q
  base := perpendicularFrame q '' planeBox A l r

lemma rectangleCylinder_base_image (q A l r : ℝ) :
    ((fun z : ((Submodule.span ℝ ({axis q} : Set Space))ᗮ) => (z : Space)) ''
      (rectangleCylinder q A l r).base) = rectangle q A l r := by
  change (fun z : ((Submodule.span ℝ ({axis q} : Set Space))ᗮ) => (z : Space)) ''
    (perpendicularFrame q '' planeBox A l r) = _
  rw [image_image, rectangle_image]
  rfl

lemma rectangleCylinder_shape {q A l r : ℝ} (hA : 0 < A) (hlr : l < r) :
    IsHorizontalRectangle (rectangleCylinder q A l r) :=
  ⟨q,A,l,r,hA,hlr,rfl,rectangleCylinder_base_image q A l r⟩

lemma rectangleCylinder_carrier (q A l r : ℝ) :
    (rectangleCylinder q A l r).carrier = cylinder q A l r := by
  ext z
  constructor
  · rintro ⟨b,hb,t,rfl⟩
    refine ⟨(b : Space),?_,t,rfl⟩
    rw [← rectangleCylinder_base_image q A l r]
    exact ⟨b,hb,rfl⟩
  · rintro ⟨b,hb,t,rfl⟩
    rw [← rectangleCylinder_base_image q A l r] at hb
    obtain ⟨b,hb,rfl⟩ := hb
    exact ⟨b,hb,t,rfl⟩

lemma perpendicular_finrank (q : ℝ) :
    Module.finrank ℝ ((Submodule.span ℝ ({axis q} : Set Space))ᗮ) = 2 := by
  have hne : axis q ≠ 0 := by
    intro hz
    have := axis_norm q
    simp [hz] at this
  have hd := (Submodule.span ℝ ({axis q} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

lemma rectangleCylinder_area {q A l r : ℝ} (hA : 0 ≤ A) (hlr : l ≤ r) :
    (rectangleCylinder q A l r).area = 2*A*(r-l) := by
  have hm := (perpendicularFrame q).toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (planeBox A l r)
  simp only [finrank_euclideanSpace_fin, LinearIsometry.normDet_eq_one,
    ENNReal.ofReal_one, one_mul] at hm
  have he : (Measure.euclideanHausdorffMeasure 2 :
      Measure ((Submodule.span ℝ ({axis q} : Set Space))ᗮ)) = volume := by
    convert InnerProductSpace.euclideanHausdorffMeasure_eq_volume using 1
    rw [perpendicular_finrank]
  change (volume (perpendicularFrame q '' planeBox A l r)).toReal = _
  rw [← he]
  change (Measure.euclideanHausdorffMeasure 2
      ((perpendicularFrame q).toLinearMap '' planeBox A l r)).toReal = _
  rw [hm]
  exact planeBox_volume hA hlr

lemma rectangleCylinder_compact (q A l r : ℝ) :
    IsCompact (rectangleCylinder q A l r).base := by
  apply IsCompact.image _ (perpendicularFrame q).continuous
  exact isCompact_Icc.image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous

lemma denominator_ge_one (q : ℝ) : 1 ≤ denominator q := by
  have hs := denominator_sq q
  have hn := denominator_pos q
  nlinarith [sq_nonneg q]

lemma coordinate_decomposition (q β x y t : ℝ) :
    vec (β*x) (β*y) t =
      (β*((1+q)*x+(1-q)*y)/denominator q) • normal q + t • vertical +
      (β*((1-q)*x-(1+q)*y)/denominator q) • axis q := by
  have hn := (denominator_pos q).ne'
  ext i
  fin_cases i <;> simp [vec, normal, axis, vertical]
  · field_simp [hn]
    linear_combination β*x*(denominator_sq q)
  · field_simp [hn]
    linear_combination β*y*(denominator_sq q)

lemma mem_cylinder_of_frozen_bound {q β x y t A l r : ℝ}
    (ht : t ∈ Icc l r)
    (hs : |β*((1+q)*x+(1-q)*y)/denominator q| ≤ A) :
    vec (β*x) (β*y) t ∈ cylinder q A l r := by
  refine ⟨(β*((1+q)*x+(1-q)*y)/denominator q) • normal q + t • vertical,
    ?_, β*((1-q)*x-(1+q)*y)/denominator q, coordinate_decomposition q β x y t⟩
  exact ⟨_, abs_le.mp hs, t, ht, rfl⟩

lemma frozen_scalar_bound {q q₀ W W₀ M η x y : ℝ}
    (hη : 0 ≤ η) (hx : |x| ≤ M) (hy : |y| ≤ M)
    (hq : |q-q₀| ≤ η) (hW : |W-W₀| ≤ η)
    (hstrip : |(1+q)*x+(1-q)*y| ≤ W) :
    |(1+q₀)*x+(1-q₀)*y| ≤ W₀+(1+2*M)*η := by
  have hM : 0 ≤ M := le_trans (abs_nonneg x) hx
  have hxy : |x-y| ≤ 2*M := by
    calc |x-y| ≤ |x|+|y| := abs_sub x y
         _ ≤ 2*M := by linarith
  have hq' : |q₀-q| ≤ η := by simpa only [abs_sub_comm q₀ q] using hq
  have hprod : |(q₀-q)*(x-y)| ≤ η*(2*M) := by
    rw [abs_mul]
    exact mul_le_mul hq' hxy (abs_nonneg _) hη
  have hW' : W ≤ W₀+η := by linarith [(abs_le.mp hW).2]
  calc |(1+q₀)*x+(1-q₀)*y|
      = |((1+q)*x+(1-q)*y)+(q₀-q)*(x-y)| := by congr 1; ring
    _ ≤ |(1+q)*x+(1-q)*y| + |(q₀-q)*(x-y)| := abs_add_le _ _
    _ ≤ W₀+(1+2*M)*η := by linarith

lemma frozen_rectangle_covers {q q₀ W W₀ M η x y t β l r : ℝ}
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hx : |x| ≤ M) (hy : |y| ≤ M)
    (hq : |q-q₀| ≤ η) (hW : |W-W₀| ≤ η)
    (hstrip : |(1+q)*x+(1-q)*y| ≤ W) (ht : t ∈ Icc l r) :
    vec (β*x) (β*y) t ∈
      cylinder q₀ (β*(W₀+(1+2*M)*η)/denominator q₀) l r := by
  apply mem_cylinder_of_frozen_bound ht
  rw [abs_div, abs_mul, abs_of_nonneg hβ, abs_of_pos (denominator_pos q₀)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (frozen_scalar_bound hη hx hy hq hW hstrip) hβ)
    (denominator_pos q₀).le

end CylinderCovering.BeamStrip

end

end OAI
