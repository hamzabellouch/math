import OAI.Geometry.Arnold.Model

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample

namespace Quadric

/-- The linear involution fixing the first coordinate. -/
def involutionLinear : CV ≃ₗ[ℂ] CV where
  toFun z j := if j = 0 then z j else -z j
  invFun z j := if j = 0 then z j else -z j
  left_inv z := by funext j; by_cases hj : j = 0 <;> simp [hj]
  right_inv z := by funext j; by_cases hj : j = 0 <;> simp [hj]
  map_add' z w := by funext j; by_cases hj : j = 0 <;> simp [hj, add_comm]
  map_smul' a z := by funext j; by_cases hj : j = 0 <;> simp [hj]

@[simp] lemma involutionLinear_apply (z : CV) (j : Fin 5) :
    involutionLinear z j = if j = 0 then z j else -z j := rfl

@[simp] lemma involutionLinear_twice (z : CV) :
    involutionLinear (involutionLinear z) = z := involutionLinear.left_inv z

@[simp] lemma involutionLinear_quadricPolynomial (z : CV) :
    quadricPolynomial (involutionLinear z) = quadricPolynomial z := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0 <;> simp [hj]

@[simp] lemma involutionLinear_normSquared (z : CV) :
    normSquared (involutionLinear z) = normSquared z := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0 <;> simp [hj]

lemma involutionLinear_unit (z : UnitQuadric) : IsUnitQuadric (involutionLinear z) := by
  simpa only [IsUnitQuadric, involutionLinear_quadricPolynomial,
    involutionLinear_normSquared] using z.property

/-- An injective complex-linear symmetry of the cone acts on the actual
projective quadric, not on a substitute abstract model. -/
lemma linearEquiv_ne_zero (D : CV ≃ₗ[ℂ] CV) {z : CV} (hz : z ≠ 0) : D z ≠ 0 := by
  intro h
  exact hz (D.injective (by simpa using h))

def map (D : CV ≃ₗ[ℂ] CV)
    (hD : ∀ z, quadricPolynomial z = 0 → quadricPolynomial (D z) = 0) : Q3 → Q3 :=
  fun q ↦ ⟨Projectivization.map D.toLinearMap D.injective q.val, by
    obtain ⟨z, hz, hq, hpoly⟩ := q.property
    refine ⟨D z, linearEquiv_ne_zero D hz, ?_, hD z hpoly⟩
    rw [← hq]
    rfl⟩

lemma map_mk (D : CV ≃ₗ[ℂ] CV)
    (hD : ∀ z, quadricPolynomial z = 0 → quadricPolynomial (D z) = 0)
    (z : CV) (hz : z ≠ 0) (hp : quadricPolynomial z = 0) :
    map D hD ⟨Projectivization.mk ℂ z hz, z, hz, rfl, hp⟩ =
      ⟨Projectivization.mk ℂ (D z) (linearEquiv_ne_zero D hz),
        D z, linearEquiv_ne_zero D hz, rfl, hD z hp⟩ := rfl

/-- The Hamiltonian involution's underlying projective equivalence. -/
def involution : Q3 ≃ Q3 where
  toFun := map involutionLinear (fun z hz ↦ by simpa using hz)
  invFun := map involutionLinear (fun z hz ↦ by simpa using hz)
  left_inv q := by
    apply Subtype.ext
    obtain ⟨z, hz, hq, hp⟩ := q.property
    change Projectivization.map involutionLinear.toLinearMap involutionLinear.injective
      (Projectivization.map involutionLinear.toLinearMap involutionLinear.injective q.val) = q.val
    rw [← hq]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, involutionLinear_twice]
  right_inv q := by
    apply Subtype.ext
    obtain ⟨z, hz, hq, hp⟩ := q.property
    change Projectivization.map involutionLinear.toLinearMap involutionLinear.injective
      (Projectivization.map involutionLinear.toLinearMap involutionLinear.injective q.val) = q.val
    rw [← hq]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, involutionLinear_twice]

@[simp] theorem involution_sq (q : Q3) : involution (involution q) = q :=
  involution.left_inv q

lemma involution_project (z : UnitQuadric) :
    involution (project z) = project ⟨involutionLinear z, involutionLinear_unit z⟩ := rfl

/-- The +1 eigenline is not on the quadric. All projectively fixed lines
therefore lie in precisely the hyperplane z0=0. -/
theorem involution_fixed_project_iff (z : UnitQuadric) :
    involution (project z) = project z ↔ (z : CV) 0 = 0 := by
  rw [involution_project]
  change (Subtype.mk _ _ : Q3) = Subtype.mk _ _ ↔ _
  rw [Subtype.mk.injEq, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    by_contra hz0
    have hzero := congrFun ha 0
    simp only [Pi.smul_apply, smul_eq_mul, involutionLinear_apply] at hzero
    have ha1 : a = 1 := mul_right_cancel₀ hz0 (by simpa using hzero)
    have hj0 : ∀ j : Fin 5, j ≠ 0 → (z : CV) j = 0 := by
      intro j hj
      have hh := congrFun ha j
      simp only [Pi.smul_apply, smul_eq_mul, ha1, one_mul, involutionLinear_apply,
        ite_eq_right hj] at hh
      linear_combination (1 / 2 : ℂ) * hh
    have hp : quadricPolynomial z = (z : CV) 0 ^ 2 := by
      apply Finset.sum_eq_single 0
      · intro j _ hj
        simp [hj0 j hj]
      · simp
    have hsq : (z : CV) 0 ^ 2 = 0 := hp.symm.trans z.property.2
    exact hz0 (sq_eq_zero_iff.mp hsq)
  · intro hz0
    refine ⟨-1, ?_⟩
    funext j
    by_cases hj : j = 0
    · subst j
      simp [hz0]
    · simp [hj]

end Quadric
end ArnoldCounterexample

end

end OAI
