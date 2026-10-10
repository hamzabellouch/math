import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Radial.Triangle

namespace OAI

noncomputable section
namespace RadialProjection
open TriangularCovering Set MeasureTheory
open scoped InnerProductSpace

lemma cross3_cross_right (u v w : Space) :
    cross3 u (cross3 v w) = (inner ℝ u w) • v - (inner ℝ u v) • w := by
  ext i
  fin_cases i <;> simp [cross3_coord, inner_coord] <;> ring

lemma cross3_normal {e a b : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0) :
    cross3 a b = (inner ℝ e (cross3 a b)) • e := by
  have hc : cross3 e (cross3 a b) = 0 := by
    rw [cross3_cross_right, ha, hb]
    simp
  have hh := cross3_cross_right e e (cross3 a b)
  rw [hc] at hh
  have hz : cross3 e 0 = 0 := by
    ext i
    fin_cases i <;> simp [cross3_coord]
  rw [hz, real_inner_self_eq_norm_sq, he, one_pow, one_smul] at hh
  exact (sub_eq_zero.mp hh.symm).symm

lemma sideways_norm {e w : Space} (he : ‖e‖ = 1)
    (hw : inner ℝ e w = 0) : ‖e + w‖ = Real.sqrt (1 + ‖w‖ ^ 2) := by
  have hsq : ‖e + w‖ ^ 2 = 1 + ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, he, hw]
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

lemma sideways_ne_zero {e w : Space} (he : ‖e‖ = 1)
    (hw : inner ℝ e w = 0) : e + w ≠ 0 := by
  intro h
  have hn := sideways_norm he hw
  rw [h, norm_zero] at hn
  have hp : 0 < Real.sqrt (1 + ‖w‖ ^ 2) := by positivity
  linarith

lemma normal_cross_abs {e a b : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0) :
    |inner ℝ e (cross3 a b)| =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  have hh := triple_gram_identity e a b
  rw [ha, hb, real_inner_self_eq_norm_sq e, he] at hh
  norm_num at hh
  rw [real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq b,
    ← hh, Real.sqrt_sq_eq_abs]

theorem normal_projection_factor {e a b w : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) :
    |inner ℝ (unit (e + w)) (cross3 a b)| =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) /
        Real.sqrt (1 + ‖w‖ ^ 2) := by
  have hcrossw : inner ℝ w (cross3 a b) = 0 := by
    rw [cross3_normal he ha hb, inner_smul_right, real_inner_comm e w, hw]
    simp
  rw [TriangularCovering.unit, inner_smul_left, inner_add_left, hcrossw, add_zero]
  simp only [conj_trivial, abs_mul, abs_inv, abs_norm]
  rw [normal_cross_abs he ha hb, sideways_norm he hw]
  ring

lemma cross3_coordinates (a b : Space) (u₁ v₁ u₂ v₂ : ℝ) :
    cross3 (u₁ • a + v₁ • b) (u₂ • a + v₂ • b) =
      (u₁ * v₂ - v₁ * u₂) • cross3 a b := by
  ext i
  fin_cases i <;> simp [cross3_coord] <;> ring

lemma collar_cross (p₀ a b : Space) (l r m d : ℝ) :
    cross3
      ((p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
        (p₀ + l • a + (m * l) • b))
      ((p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
        (p₀ + l • a + (m * l) • b)) =
      (d * (r - l) ^ 2) • cross3 a b := by
  have h₁ : (p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
      (p₀ + l • a + (m * l) • b) =
      (r - l) • a + (m * (r - l) - d / 2 * (r - l)) • b := by module
  have h₂ : (p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
      (p₀ + l • a + (m * l) • b) =
      (r - l) • a + (m * (r - l) + d / 2 * (r - l)) • b := by module
  rw [h₁, h₂, cross3_coordinates]
  congr 1
  ring

theorem collar_projection_area (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 ≤ d) :
    area (projection (TriangularCovering.unit (e + w)) '' triangle
      (p₀ + l • a + (m * l) • b)
      (p₀ + r • a + (m * r - d / 2 * (r - l)) • b)
      (p₀ + r • a + (m * r + d / 2 * (r - l)) • b)) =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) *
        d * (r - l) ^ 2 / (2 * Real.sqrt (1 + ‖w‖ ^ 2)) := by
  unfold area
  rw [projection_triangle_measure (unit_norm (sideways_ne_zero he hw)),
    ENNReal.toReal_ofReal (by positivity), collar_cross, inner_smul_right,
    abs_mul, abs_of_nonneg (mul_nonneg hd (sq_nonneg _)),
    normal_projection_factor he ha hb hw]
  ring

theorem collar_projection_nondegenerate (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 < d) (hlr : l < r)
    (hκ : 0 < Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2)) :
    inner ℝ (TriangularCovering.unit (e + w))
      (cross3
        ((p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
          (p₀ + l • a + (m * l) • b))
        ((p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
          (p₀ + l • a + (m * l) • b))) ≠ 0 := by
  rw [← abs_pos, collar_cross, inner_smul_right, abs_mul,
    abs_of_nonneg (mul_nonneg hd.le (sq_nonneg _)), normal_projection_factor he ha hb hw]
  exact mul_pos (mul_pos hd (sq_pos_of_pos (sub_pos.mpr hlr))) (div_pos hκ (by positivity))

lemma gram_sqrt_pos {a b : Space}
    (hab : LinearIndependent ℝ (![a, b] : Fin 2 → Space)) :
    0 < Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  have hpi : LinearIndependent ℝ (![a.ofLp, b.ofLp] : Fin 2 → (Fin 3 → ℝ)) := by
    have hh := hab.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
      (LinearMap.ker_eq_bot.mpr (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun : (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap ∘
        (![a, b] : Fin 2 → Space) = ![a.ofLp, b.ofLp] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at hh
    exact hh
  have hc : cross3 a b ≠ 0 := by
    intro hz
    apply (crossProduct_ne_zero_iff_linearIndependent.mpr hpi)
    simpa [cross3] using congrArg WithLp.ofLp hz
  rw [← cross3_gram, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr hc

def coordinateAffine (p₀ a b : Space) : (ℝ × ℝ) →ᵃ[ℝ] Space where
  toFun := fun p => p₀ + p.1 • a + p.2 • b
  linear := (LinearMap.fst ℝ ℝ ℝ).smulRight a + (LinearMap.snd ℝ ℝ ℝ).smulRight b
  map_vadd' := by
    intro p v
    simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, LinearMap.add_apply,
      LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    module

lemma coordinate_region_image (p₀ a b : Space) {l r m d : ℝ}
    (hlr : l < r) (hd : 0 < d) :
    coordinateAffine p₀ a b '' CylinderCovering.RadialTriangle.region l r m d =
      triangle (p₀ + l • a + (m * l) • b)
        (p₀ + r • a + (m * r - d / 2 * (r - l)) • b)
        (p₀ + r • a + (m * r + d / 2 * (r - l)) • b) := by
  rw [CylinderCovering.RadialTriangle.region_eq_convexHull hlr hd,
    (coordinateAffine p₀ a b).image_convexHull, triangle]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem exists_collar_cylinder_exact (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 < d) (hlr : l < r)
    (hab : LinearIndependent ℝ (![a, b] : Fin 2 → Space)) :
    ∃ c : TriCylinder,
      c.axis = TriangularCovering.unit (e + w) ∧
      c.base = projection (TriangularCovering.unit (e + w)) '' triangle
        (p₀ + l • a + (m * l) • b)
        (p₀ + r • a + (m * r - d / 2 * (r - l)) • b)
        (p₀ + r • a + (m * r + d / 2 * (r - l)) • b) ∧
      area c.base = Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) *
        d * (r - l) ^ 2 / (2 * Real.sqrt (1 + ‖w‖ ^ 2)) ∧
      ∀ u v s : ℝ, l ≤ u → u ≤ r → |v - m * u| ≤ d / 2 * (u - l) →
        p₀ + u • a + v • b + s • (e + w) ∈ c.carrier := by
  let P := p₀ + l • a + (m * l) • b
  let Q := p₀ + r • a + (m * r - d / 2 * (r - l)) • b
  let R := p₀ + r • a + (m * r + d / 2 * (r - l)) • b
  have hv := sideways_ne_zero he hw
  have hcross := collar_projection_nondegenerate p₀ e a b w l r m d
    he ha hb hw hd hlr (gram_sqrt_pos hab)
  refine ⟨projectedCylinder (TriangularCovering.unit (e + w)) (unit_norm hv)
    P Q R hcross, rfl, rfl, ?_, ?_⟩
  · exact collar_projection_area p₀ e a b w l r m d he ha hb hw hd.le
  · intro u v s hlu hur huv
    have hp : p₀ + u • a + v • b ∈ triangle P Q R := by
      rw [← coordinate_region_image p₀ a b hlr hd]
      exact ⟨(u, v), ⟨hlu, hur, huv⟩, rfl⟩
    exact projectedCylinder_mem_direction (e + w) hv P Q R hcross hp s rfl

theorem exists_collar_cylinder (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 < d) (hlr : l < r)
    (hab : LinearIndependent ℝ (![a, b] : Fin 2 → Space)) :
    ∃ c : TriCylinder,
      c.axis = TriangularCovering.unit (e + w) ∧
      area c.base = Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) *
        d * (r - l) ^ 2 / (2 * Real.sqrt (1 + ‖w‖ ^ 2)) ∧
      ∀ u v s : ℝ, l ≤ u → u ≤ r → |v - m * u| ≤ d / 2 * (u - l) →
        p₀ + u • a + v • b + s • (e + w) ∈ c.carrier := by
  obtain ⟨c, haxis, _, harea, hcover⟩ :=
    exists_collar_cylinder_exact p₀ e a b w l r m d he ha hb hw hd hlr hab
  exact ⟨c, haxis, harea, hcover⟩

end RadialProjection

end

end OAI
