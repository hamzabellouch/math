import OAI.Analysis.BoundedHochschild.TracialDecomposition

namespace OAI

/-!
# Type I structure of full operator algebras

Every nonzero operator projection dominates a nonzero abelian rank-one
projection. This verifies the type-I condition used in the classical
vanishing input. In particular a full operator algebra has no type II₁
central summand. No trace or cohomological vanishing is assumed.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A nonzero operator has a vector on which it is nonzero. -/
lemma exists_apply_ne_zero {T : H →L[ℂ] H} (hT : T ≠ 0) : ∃ x : H, T x ≠ 0 := by
  by_contra h
  push Not at h
  apply hT
  ext x
  exact h x

/-- A nonzero projection fixes a unit vector. -/
lemma projection_fixes_unit_vector {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) : ∃ x : H, ‖x‖ = 1 ∧ p x = x := by
  obtain ⟨y, hy⟩ := exists_apply_ne_zero hp0
  have hpy : p (p y) = p y := congrArg (fun T : H →L[ℂ] H => T y) hp.isIdempotentElem.eq
  refine ⟨(‖p y‖⁻¹ : ℂ) • p y, norm_smul_inv_norm hy, ?_⟩
  rw [map_smul, hpy]

/-- A rank-one orthogonal projection has an abelian corner. -/
lemma rankOne_abelian (x : H) (hx : ‖x‖ = 1) :
    ∃ hq : IsStarProjection (InnerProductSpace.rankOne ℂ x x),
      PopaTypeII.AbelianProjection hq := by
  let q := InnerProductSpace.rankOne ℂ x x
  have hq : IsStarProjection q := by
    constructor
    · exact InnerProductSpace.isIdempotentElem_rankOne_self hx
    · change star q = q
      simp only [q, ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  refine ⟨hq, ?_⟩
  have hscalar (A : PopaCorner.algebra hq) :
      (A : H →L[ℂ] H) = (inner ℂ x ((A : H →L[ℂ] H) x)) • q := by
    ext y
    have hleft := congrArg (fun T : H →L[ℂ] H => T y) A.property.1
    have hright := congrArg (fun T : H →L[ℂ] H => T y) A.property.2
    change q ((A : H →L[ℂ] H) y) = (A : H →L[ℂ] H) y at hleft
    change (A : H →L[ℂ] H) (q y) = (A : H →L[ℂ] H) y at hright
    calc
      (A : H →L[ℂ] H) y = q ((A : H →L[ℂ] H) y) := hleft.symm
      _ = q ((A : H →L[ℂ] H) (q y)) := by rw [hright]
      _ = (inner ℂ x ((A : H →L[ℂ] H) x)) • q y := by
        simp only [q, InnerProductSpace.rankOne_apply, map_smul,
          smul_smul, mul_comm]
  intro A B
  apply Subtype.ext
  change (A : H →L[ℂ] H) * (B : H →L[ℂ] H) =
    (B : H →L[ℂ] H) * (A : H →L[ℂ] H)
  rw [hscalar A, hscalar B, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm]

/-- Every nonzero operator projection contains a rank-one abelian projection. -/
theorem operator_projection_has_abelian_subprojection {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : H →L[ℂ] H, ∃ hq : IsStarProjection q,
      q ≤ p ∧ q ≠ 0 ∧ PopaTypeII.AbelianProjection hq := by
  obtain ⟨x, hx, hpx⟩ := projection_fixes_unit_vector hp hp0
  let q := InnerProductSpace.rankOne ℂ x x
  obtain ⟨hq, hqa⟩ := rankOne_abelian x hx
  have hqle : q ≤ p := by
    apply (hq.le_iff_mul_eq_right hp).mpr
    ext y
    change p (q y) = q y
    simp only [q, InnerProductSpace.rankOne_apply, map_smul, hpx]
  have hqx : q x = x := by
    norm_num [q, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hx]
  have hq0 : q ≠ 0 := by
    intro hzero
    have hzero' : x = 0 := by simpa only [hzero, zero_apply] using hqx.symm
    have h01 : (0 : ℝ) = 1 := by simpa only [hzero', norm_zero] using hx
    exact zero_ne_one h01
  exact ⟨q, hq, hqle, hq0, hqa⟩

section Equivalence
variable {N : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

lemma map_starProjection (φ : N ≃⋆ₐ[ℂ] (H →L[ℂ] H)) {p : N}
    (hp : IsStarProjection p) : IsStarProjection (φ p) := by
  constructor
  · change φ p * φ p = φ p
    rw [← map_mul, hp.isIdempotentElem.eq]
  · change star (φ p) = φ p
    rw [← map_star, hp.isSelfAdjoint.star_eq]

lemma abelianProjection_of_map (φ : N ≃⋆ₐ[ℂ] (H →L[ℂ] H)) {p : N}
    (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection (map_starProjection φ hp)) :
    PopaTypeII.AbelianProjection hp := by
  let push (a : PopaCorner.algebra hp) : PopaCorner.algebra (map_starProjection φ hp) :=
    ⟨φ (a : N), by
      constructor
      · change φ p * φ (a : N) = φ (a : N)
        rw [← map_mul, a.property.1]
      · change φ (a : N) * φ p = φ (a : N)
        rw [← map_mul, a.property.2]⟩
  intro a b
  apply Subtype.ext
  apply φ.injective
  change φ ((a : N) * (b : N)) = φ ((b : N) * (a : N))
  have hh := congrArg (fun c : PopaCorner.algebra (map_starProjection φ hp) =>
    (c : H →L[ℂ] H)) (hpa (push a) (push b)).eq
  change φ (a : N) * φ (b : N) = φ (b : N) * φ (a : N) at hh
  simpa only [map_mul] using hh

/-- An actual full-operator-algebra presentation satisfies the type I condition. -/
theorem typeICorner_one_of_operator_equiv (φ : N ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    PopaTypeII.TypeICorner (IsStarProjection.one N) := by
  intro p hp _ hp0
  have hφp := map_starProjection φ hp
  have hφp0 : φ p ≠ 0 := by
    intro hzero
    apply hp0
    apply φ.injective
    change φ p = φ 0
    simpa only [map_zero] using hzero
  obtain ⟨q, hq, hqp, hq0, hqa⟩ := operator_projection_has_abelian_subprojection hφp hφp0
  let r := φ.symm q
  have hr : IsStarProjection r := by
    constructor
    · change φ.symm q * φ.symm q = φ.symm q
      rw [← map_mul, hq.isIdempotentElem.eq]
    · change star (φ.symm q) = φ.symm q
      rw [← map_star, hq.isSelfAdjoint.star_eq]
  have hrp : r ≤ p := by
    apply (hr.le_iff_mul_eq_left hp).mpr
    apply φ.injective
    change φ (r * p) = φ r
    rw [map_mul]
    change φ (φ.symm q) * φ p = φ (φ.symm q)
    rw [φ.apply_symm_apply]
    exact (hq.le_iff_mul_eq_left hφp).mp hqp
  have hr0 : r ≠ 0 := by
    intro hr0
    apply hq0
    have h := congrArg φ hr0
    simpa only [r, φ.apply_symm_apply, map_zero] using h
  refine ⟨r, hr, hrp, hr0, abelianProjection_of_map φ hr ?_⟩
  simpa only [r, φ.apply_symm_apply] using hqa

end Equivalence

/-- A central operator projection is either zero or the identity. -/
theorem central_operator_projection_eq_one {z : H →L[ℂ] H} (hz : IsStarProjection z)
    (hc : ∀ T : H →L[ℂ] H, z * T = T * z) (hz0 : z ≠ 0) : z = 1 := by
  obtain ⟨x, hx, hzx⟩ := projection_fixes_unit_vector hz hz0
  obtain ⟨φ, _hφn, hφx⟩ := exists_dual_vector ℂ x (by rw [hx]; norm_num)
  have hφ : φ x = 1 := by simpa [hx] using hφx
  ext y
  have h := congrArg (fun T : H →L[ℂ] H => T x) (hc (rankOneColumn φ y))
  change z ((rankOneColumn φ y) x) = (rankOneColumn φ y) (z x) at h
  simpa only [rankOneColumn_apply, hzx, hφ, one_smul, one_apply_eq_self] using h

/-- Full operator algebras have no type II₁ central summand. -/
theorem operators_noTypeII1Summand : NoTypeII1Summand (H →L[ℂ] H) := by
  intro z hz hc _hfinite hnoI
  by_contra hz0
  have hz1 := central_operator_projection_eq_one hz hc hz0
  subst z
  let N := Corner (1 : H →L[ℂ] H) hz
  have hN1 : (1 : N) ≠ 0 := by
    intro hzero
    apply hz0
    exact congrArg (fun a : N => (a : H →L[ℂ] H)) hzero
  exact hnoI 1 (IsStarProjection.one N) (fun _ => Commute.one_left _) hN1
    (typeICorner_one_of_operator_equiv unitCornerEquiv)

end KadisonRingrose
end BoundedHochschild

end

end OAI
