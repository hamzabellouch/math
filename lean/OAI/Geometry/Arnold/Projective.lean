import OAI.Geometry.Arnold.Involution

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

lemma normSquared_eq_zero_iff (z : CV) : normSquared z = 0 ↔ z = 0 := by
  rw [normSquared, Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))]
  simp only [Finset.mem_univ, forall_const, Complex.normSq_eq_zero]
  exact ⟨fun h ↦ funext h, fun h j ↦ congrFun h j⟩

lemma normSquared_nonneg (z : CV) : 0 ≤ normSquared z :=
  Finset.sum_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))

lemma normSquared_pos {z : CV} (hz : z ≠ 0) : 0 < normSquared z :=
  lt_of_le_of_ne (normSquared_nonneg z) (Ne.symm (mt (normSquared_eq_zero_iff z).mp hz))

lemma quadricPolynomial_smul (a : ℂ) (z : CV) :
    quadricPolynomial (a • z) = a ^ 2 * quadricPolynomial z := by
  simp only [quadricPolynomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma normSquared_smul (a : ℂ) (z : CV) :
    normSquared (a • z) = Complex.normSq a * normSquared z := by
  simp only [normSquared, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

/-- Every projective quadric point has a unit representative, proved without
assuming the standard quotient geometry. -/
theorem project_surjective : Function.Surjective project := by
  intro q
  obtain ⟨z, hz, hq, hp⟩ := q.property
  have hn : 0 < normSquared z := normSquared_pos hz
  have hs : 0 < Real.sqrt (normSquared z) := Real.sqrt_pos.mpr hn
  let a : ℂ := ((Real.sqrt (normSquared z))⁻¹ : ℝ)
  have ha : a ≠ 0 := by
    simp only [a, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact ne_of_gt hs
  have hnorm : normSquared (a • z) = 1 := by
    rw [normSquared_smul]
    simp only [a, Complex.normSq_ofReal]
    field_simp [ne_of_gt hs]
    nlinarith [Real.sq_sqrt hn.le]
  have hpoly : quadricPolynomial (a • z) = 0 := by
    rw [quadricPolynomial_smul, hp, mul_zero]
  refine ⟨⟨a • z, hnorm, hpoly⟩, ?_⟩
  apply Subtype.ext
  change Projectivization.mk ℂ (a • z) _ = q.val
  rw [← hq, Projectivization.mk_eq_mk_iff']
  exact ⟨a, rfl⟩

lemma horizontal_smul {z v : CV} (hv : Horizontal z v) (a : ℂ) :
    Horizontal z (a • v) := by
  constructor
  · calc
      (∑ j, star (z j) * (a • v) j) = a * ∑ j, star (z j) * v j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hv.1, mul_zero]
  · calc
      (∑ j, z j * (a • v) j) = a * ∑ j, z j * v j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hv.2, mul_zero]

lemma omega_I (v : CV) : omega v (Complex.I • v) = 2 * normSquared v := by
  unfold omega normSquared
  congr 1
  rw [show (∑ j, star (v j) * (Complex.I • v) j).im =
    ∑ j, (star (v j) * (Complex.I • v) j).im from
      by simpa only [Complex.coe_imAddGroupHom] using
        (map_sum Complex.imAddGroupHom
          (fun j : Fin 5 ↦ star (v j) * (Complex.I • v) j) Finset.univ)]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]

/-- Positivity on complex lines proves the actual horizontal form
nondegenerate, with the factor 2 normalization. -/
theorem omega_horizontal_nondegenerate {z v : CV} (hv : Horizontal z v)
    (hvanish : ∀ w : CV, Horizontal z w → omega v w = 0) : v = 0 := by
  have h := hvanish (Complex.I • v) (horizontal_smul hv Complex.I)
  rw [omega_I] at h
  have hn : normSquared v = 0 := by linarith
  exact (normSquared_eq_zero_iff v).mp hn

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

/-- Complex-bilinear pairing defining the quadric. -/
def bilinear (z w : CV) : ℂ := ∑ j, z j * w j

lemma bilinear_comm (z w : CV) : bilinear z w = bilinear w z := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinear_add_left (z w v : CV) : bilinear (z + w) v = bilinear z v + bilinear w v := by
  simp [bilinear, add_mul, Finset.sum_add_distrib]

lemma bilinear_add_right (z w v : CV) : bilinear z (w + v) = bilinear z w + bilinear z v := by
  simp [bilinear, mul_add, Finset.sum_add_distrib]

lemma bilinear_smul_left (a : ℂ) (z w : CV) : bilinear (a • z) w = a * bilinear z w := by
  simp [bilinear, Finset.mul_sum, mul_assoc]

lemma bilinear_smul_right (a : ℂ) (z w : CV) : bilinear z (a • w) = a * bilinear z w := by
  rw [bilinear_comm, bilinear_smul_left, bilinear_comm w z]

@[simp] lemma bilinear_self (z : CV) : bilinear z z = quadricPolynomial z := by
  simp [bilinear, quadricPolynomial, pow_two]

@[simp] lemma bilinear_star_self (z : CV) : bilinear (star z) z = (normSquared z : ℂ) := by
  simp only [bilinear, Pi.star_apply, normSquared]
  rw [show ((∑ j, Complex.normSq (z j) : ℝ) : ℂ) =
      ∑ j, (Complex.normSq (z j) : ℂ) from map_sum Complex.ofRealHom _ _]
  apply Finset.sum_congr rfl
  intro j _
  exact (Complex.normSq_eq_conj_mul_self).symm

lemma quadricPolynomial_star (z : CV) : quadricPolynomial (star z) = star (quadricPolynomial z) := by
  simp [quadricPolynomial, star_sum, star_pow]

lemma quadricPolynomial_add (z w : CV) :
    quadricPolynomial (z + w) = quadricPolynomial z + 2 * bilinear z w + quadricPolynomial w := by
  simp only [quadricPolynomial, bilinear, Pi.add_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The tangent space is the kernel of two independent complex linear forms. -/
def tangentConstraint (z : CV) : CV →ₗ[ℂ] ℂ × ℂ where
  toFun v := (bilinear (star z) v, bilinear z v)
  map_add' v w := by simp [bilinear_add_right]
  map_smul' a v := by simp [bilinear_smul_right]

lemma horizontal_iff_constraint {z v : CV} :
    Horizontal z v ↔ tangentConstraint z v = 0 := by
  simp [Horizontal, tangentConstraint, bilinear, Prod.ext_iff]

lemma tangentConstraint_surjective (z : UnitQuadric) :
    Function.Surjective (tangentConstraint z) := by
  rintro ⟨a, b⟩
  use a • (z : CV) + b • star (z : CV)
  have h1 : bilinear (star (z : CV)) z = 1 := by
    rw [bilinear_star_self, z.property.1, Complex.ofReal_one]
  have h2 : bilinear (z : CV) (star (z : CV)) = 1 :=
    (bilinear_comm _ _).trans h1
  have h3 : bilinear (star (z : CV)) (star (z : CV)) = 0 := by
    rw [bilinear_self, quadricPolynomial_star, z.property.2, star_zero]
  change (bilinear (star (z : CV)) _, bilinear (z : CV) _) = (a, b)
  apply Prod.ext <;> simp only [bilinear_add_right, bilinear_smul_right, h1, h2, h3,
    bilinear_self, z.property.2, mul_one, mul_zero, add_zero, zero_add]

/-- Actual complex dimension three, hence real dimension six, of the horizontal tangent. -/
theorem horizontal_finrank (z : UnitQuadric) :
    Module.finrank ℂ (LinearMap.ker (tangentConstraint z)) = 3 := by
  have h := (tangentConstraint z).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tangentConstraint_surjective z)] at h
  norm_num [Module.finrank_pi, Module.finrank_prod] at h ⊢
  omega

/-- A concrete polynomial parametrization transverse to the complex scaling.
For horizontal v it stays on the quadric and its first derivative at zero is v.
This makes the horizontal tangent identification independent of any assumed atlas. -/
def localSection (z v : CV) : CV := z + v + (-(quadricPolynomial v / 2)) • star z

lemma localSection_on_quadric (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    quadricPolynomial (localSection z v) = 0 := by
  have hzv : bilinear (z : CV) v = 0 := hv.2
  have hsv : bilinear (star (z : CV)) v = 0 := hv.1
  have hnorm : bilinear (z : CV) (star (z : CV)) = 1 := by
    rw [bilinear_comm, bilinear_star_self, z.property.1, Complex.ofReal_one]
  have hvstar : bilinear v (star (z : CV)) = 0 := (bilinear_comm _ _).trans hsv
  simp only [localSection, quadricPolynomial_add, quadricPolynomial_smul,
    bilinear_add_left, bilinear_smul_right, quadricPolynomial_star, z.property.2,
    star_zero, hnorm, hvstar, hzv]
  ring

lemma localSection_gauge (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    bilinear (star (z : CV)) (localSection z v) = 1 := by
  have hnorm : bilinear (star (z : CV)) z = 1 := by
    rw [bilinear_star_self, z.property.1, Complex.ofReal_one]
  have hsv : bilinear (star (z : CV)) v = 0 := hv.1
  simp only [localSection, bilinear_add_right, bilinear_smul_right, hnorm, hsv,
    bilinear_self, quadricPolynomial_star, z.property.2, star_zero, mul_zero, add_zero]

lemma localSection_ne_zero (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    localSection z v ≠ 0 := by
  intro h
  have hg := localSection_gauge z hv
  simp [h, bilinear] at hg

end ArnoldCounterexample.Quadric

end

end OAI
