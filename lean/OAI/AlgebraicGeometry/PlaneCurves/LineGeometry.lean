import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import OAI.AlgebraicGeometry.PlaneCurves.LineRestriction

namespace OAI

/-!
# Linear forms, projective minors, and coordinate line ideals
-/

section

/-! The scalar normal-differential input: a nonzero linear functional over a
field is onto. This proves the linear algebra; smoothness must supply the
actual nonzero differential of the chosen local curve equation. -/
namespace Nagata.Workers.W14

/-- Every nonzero linear functional realizes every prescribed scalar. -/
theorem nonzero_linearFunctional_surjective {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (L : V →ₗ[K] K) (hL : L ≠ 0) :
    Function.Surjective L := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    apply hL
    apply LinearMap.ext
    intro v
    exact Classical.not_not.mp (fun h => hn ⟨v, h⟩)
  intro c
  refine ⟨(c / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hv]

end Nagata.Workers.W14

end

section

/-! Coordinate algebra behind the projective separation minors. -/
noncomputable section
namespace Nagata.Workers.W14

/-- Vanishing of all two by two minors against a nonzero vector implies
proportionality, over the actual coefficient field. -/
theorem exists_smul_of_all_minors_zero {K ι : Type*} [Field K]
    (u v : ι → K) (hv : v ≠ 0)
    (hminor : ∀ a b, u a * v b - u b * v a = 0) :
    ∃ c : K, c • v = u := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra hnone
    apply hv
    funext b
    exact Classical.not_not.mp (fun hb => hnone ⟨b, hb⟩)
  refine ⟨u b / v b, ?_⟩
  funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  exact (div_eq_iff hb).2 (sub_eq_zero.mp (hminor b a))

/-- Scalar-multiple vectors have every two by two minor equal to zero. -/
theorem minor_zero_of_smul {K ι : Type*} [Field K]
    (u v : ι → K) (c : K) (hc : c • v = u) (a b : ι) :
    u a * v b - u b * v a = 0 := by
  have ha : c * v a = u a := congrFun hc a
  have hb : c * v b = u b := congrFun hc b
  rw [← ha, ← hb]
  ring

end Nagata.Workers.W14

end
end

section

/-! A genuine homogeneous degree-one polynomial defines its actual linear
functional; nonzero equations yield nonzero functionals. -/
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators

 theorem homogeneous_one_eq_sum {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) :
    L = ∑ i : Fin 3, MvPolynomial.monomial (Finsupp.single i 1)
      (L.coeff (Finsupp.single i 1)) := by
  classical
  ext e
  by_cases he : e.degree = 1
  · have hr : e ∈ Set.range (fun i : Fin 3 => Finsupp.single i (1 : ℕ)) := by
      rw [Finsupp.range_single_one]
      exact he
    obtain ⟨i,rfl⟩ := hr
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  · have hcoeff : L.coeff e = 0 := by
      by_contra hc
      exact he (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hL hc)
    rw [hcoeff, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : Finsupp.single i 1 ≠ e := by
      intro hi
      apply he
      rw [← hi]
      simp
    simp [MvPolynomial.coeff_monomial, hne]

 def homogeneousLinearMap {K : Type*} [Field K] (L : MvPolynomial (Fin 3) K) :
    (Fin 3 → K) →ₗ[K] K :=
  ∑ i : Fin 3, L.coeff (Finsupp.single i 1) • LinearMap.proj i

 theorem homogeneousLinearMap_apply {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) (v : Fin 3 → K) :
    homogeneousLinearMap L v = MvPolynomial.eval v L := by
  conv_rhs => rw [homogeneous_one_eq_sum L hL]
  simp [homogeneousLinearMap, MvPolynomial.eval_monomial]

 theorem homogeneousLinearMap_ne_zero (L : MvPolynomial (Fin 3) ℂ)
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) : homogeneousLinearMap L ≠ 0 := by
  intro hz
  apply hne
  apply hL.eq_zero_of_forall_eval_eq_zero
  intro v
  rw [← homogeneousLinearMap_apply L hL, hz]
  rfl

end Nagata.Workers.W14

end
end

section

/-! Actual projective equality and the vanishing of two by two minors. -/
noncomputable section
namespace Nagata.Workers.W14

/-- Distinct actual projective points have a nonzero two by two minor in
any pair of nonzero homogeneous representatives. -/
theorem exists_minor_ne_zero_of_projective_ne {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Projectivization.mk K u hu ≠ Projectivization.mk K v hv) :
    ∃ a b, u a * v b - u b * v a ≠ 0 := by
  classical
  by_contra hn
  have hminor : ∀ a b, u a * v b - u b * v a = 0 := by
    intro a b
    exact Classical.not_not.mp (fun hh => hn ⟨a, b, hh⟩)
  apply h
  exact (Projectivization.mk_eq_mk_iff' K u v hu hv).2
    (exists_smul_of_all_minors_zero u v hv hminor)

/-- A nonzero two by two minor separates the two genuine projective points. -/
theorem projective_ne_of_minor_ne_zero {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0) (a b : ι)
    (hminor : u a * v b - u b * v a ≠ 0) :
    Projectivization.mk K u hu ≠ Projectivization.mk K v hv := by
  intro heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K u v hu hv).1 heq
  exact hminor (minor_zero_of_smul u v c hc a b)

end Nagata.Workers.W14

end
end

section

/-! The actual ideal of the coordinate line X₂=0, with its binary polynomial
restriction and homogeneous degree preserved. -/
noncomputable section
namespace Nagata.Workers.W14

 def coordinateLineRestriction : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0,MvPolynomial.X 1,0]

 theorem coordinateLineRestriction_eval (Q : MvPolynomial (Fin 3) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (coordinateLineRestriction Q) =
      MvPolynomial.eval ![v 0,v 1,0] Q := by
  have h : (MvPolynomial.eval v).comp coordinateLineRestriction =
      MvPolynomial.eval ![v 0,v 1,0] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateLineRestriction]
    · intro i
      fin_cases i <;> simp [coordinateLineRestriction]
  exact RingHom.congr_fun h Q

 theorem coordinateLineRestriction_homogeneous {Q : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) : (coordinateLineRestriction Q).IsHomogeneous d := by
  have hcoords : ∀ i : Fin 3,
      (![MvPolynomial.X 0,MvPolynomial.X 1,0] i : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_zero (Fin 2) ℂ 1
  simpa only [coordinateLineRestriction, MvPolynomial.coe_eval₂Hom, one_mul] using hQ.eval₂ MvPolynomial.C
    ![MvPolynomial.X 0,MvPolynomial.X 1,0]
    (fun c => MvPolynomial.isHomogeneous_C (Fin 2) c) hcoords

 def polynomialInLastCoordinate : MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ]
    Polynomial (MvPolynomial (Fin 2) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).trans
    (MvPolynomial.finSuccEquiv ℂ 2)

 theorem polynomialInLastCoordinate_X : polynomialInLastCoordinate (MvPolynomial.X 2) =
    Polynomial.X := by
  simp [polynomialInLastCoordinate, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_apply]

 theorem polynomialInLastCoordinate_eval_zero (Q : MvPolynomial (Fin 3) ℂ) :
    (polynomialInLastCoordinate Q).eval 0 =
      MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (coordinateLineRestriction Q) := by
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) ℂ)).comp
      polynomialInLastCoordinate.toRingHom =
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom.comp coordinateLineRestriction := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialInLastCoordinate, coordinateLineRestriction,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i <;> simp [polynomialInLastCoordinate, coordinateLineRestriction,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply, Equiv.swap_apply_def]
      all_goals
        change Polynomial.eval 0 (Polynomial.C _) = _
        simp
  exact RingHom.congr_fun h Q

 theorem coordinateLine_dvd_of_restriction_zero (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : coordinateLineRestriction Q = 0) : MvPolynomial.X 2 ∣ Q := by
  rw [← map_dvd_iff polynomialInLastCoordinate, polynomialInLastCoordinate_X]
  apply Polynomial.X_dvd_iff.mpr
  rw [Polynomial.coeff_zero_eq_eval_zero,polynomialInLastCoordinate_eval_zero,hQ]
  simp

end Nagata.Workers.W14

end
end

end OAI
