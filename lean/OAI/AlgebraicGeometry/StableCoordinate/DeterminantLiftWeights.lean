import OAI.AlgebraicGeometry.StableCoordinate.FrameScaling
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantWeights
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantDomain
import OAI.AlgebraicGeometry.StableCoordinate.BundleCharts

namespace OAI

/-!
# Fiber-weight compatibility of normalized lifts on the determinant quotient

This specializes normalized-frame uniqueness to the actual source rings and the
actual Laurent fiber coaction.  A normalized polynomial lift extending a base
polynomial family has the exact fiber weights coefficient by coefficient; no
fiber-linearity or equivariance is assumed of the chosen lift.
-/

noncomputable section
namespace StableCoordinate.DeterminantLiftWeights

open Polynomial FrameLift DeterminantRing DeterminantWeights

variable (k : Type*) [Field k]

-- Fix the polynomial coefficient structure to the commutative-ring projection.
-- It is definitionally the usual Laurent semiring, but this guides inference
-- through Polynomial's semiring-indexed type.
local instance laurentSemiring : Semiring (LaurentPolynomial (C k)) :=
  (inferInstance : CommRing (LaurentPolynomial (C k))).toSemiring

local instance determinantDomain : IsDomain (C k) :=
  DeterminantDomain.determinantRing_isDomain k

/-- The original determinant frame on `SL₂ × A¹`. -/
def sourceFrame : Frame (C k) where
  a := a k
  d := d k
  b := b k
  c := c k
  determinant := determinant_relation k

/-- The invertible Laurent parameter of fiber scaling. -/
def parameterUnit : (LaurentPolynomial (C k))ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

/-- Constant Laurent polynomials as a base-algebra map. -/
def constants : C k →ₐ[k] LaurentPolynomial (C k) where
  toRingHom := LaurentPolynomial.C
  commutes' := by intro r; rfl

@[simp] theorem constants_apply (r : C k) : constants k r = LaurentPolynomial.C r := rfl

/-- The actual base-quadric inclusion; definitions agree with the chart API. -/
abbrev quadricMap : BundleCharts.QuadricRing k →ₐ[k] C k := BundleCharts.baseMap k

/-- The original source frame has the prescribed scaling, with no assumption. -/
theorem sourceFrame_scales :
    (sourceFrame k).map (fiberCoaction k).toRingHom =
      Frame.scale (R := LaurentPolynomial (C k))
        ((sourceFrame k).map (constants k).toRingHom) (parameterUnit k) := by
  apply Frame.ext
  · change fiberCoaction k (a k) = LaurentPolynomial.T 1 * LaurentPolynomial.C (a k)
    rw [fiberCoaction_a, LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm (LaurentPolynomial.C (a k)) (LaurentPolynomial.T 1)
  · change fiberCoaction k (d k) = LaurentPolynomial.T 1 * LaurentPolynomial.C (d k)
    rw [fiberCoaction_d, LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm (LaurentPolynomial.C (d k)) (LaurentPolynomial.T 1)
  · change fiberCoaction k (b k) = LaurentPolynomial.T (-1) * LaurentPolynomial.C (b k)
    rw [fiberCoaction_b, LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm (LaurentPolynomial.C (b k)) (LaurentPolynomial.T (-1))
  · change fiberCoaction k (c k) = LaurentPolynomial.T (-1) * LaurentPolynomial.C (c k)
    rw [fiberCoaction_c, LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm (LaurentPolynomial.C (c k)) (LaurentPolynomial.T (-1))

/-- The base-quadric subalgebra is fixed by the fiber coaction. -/
theorem fiberCoaction_quadricMap :
    (fiberCoaction k).comp (quadricMap k) = (constants k).comp (quadricMap k) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fiberCoaction k (BundleCharts.baseMap k (BundleCharts.qgen k i)) =
    constants k (BundleCharts.baseMap k (BundleCharts.qgen k i))
  rw [BundleCharts.baseMap_qgen]
  fin_cases i
  · change fiberCoaction k (a k * b k) = LaurentPolynomial.C (a k * b k)
    rw [map_mul, fiberCoaction_a, fiberCoaction_b, AddMonoidAlgebra.single_mul_single]
    norm_num [LaurentPolynomial.single_eq_C]
  · change fiberCoaction k (d k * c k) = LaurentPolynomial.C (d k * c k)
    rw [map_mul, fiberCoaction_d, fiberCoaction_c, AddMonoidAlgebra.single_mul_single]
    norm_num [LaurentPolynomial.single_eq_C]
  · change fiberCoaction k (d k * b k) = LaurentPolynomial.C (d k * b k)
    rw [map_mul, fiberCoaction_d, fiberCoaction_b, AddMonoidAlgebra.single_mul_single]
    norm_num [LaurentPolynomial.single_eq_C]
  · change fiberCoaction k (u k) = LaurentPolynomial.C (u k)
    rw [fiberCoaction_u, LaurentPolynomial.single_eq_C]

/-- A normalized polynomial frame above three base polynomial functions is
fiber-equivariant in the source's actual determinant ring. -/
theorem normalized_lift_scaling
    (F : Frame (C k)[X]) (x y z : (BundleCharts.QuadricRing k)[X])
    (hx : F.a * F.b = x.map (quadricMap k).toRingHom)
    (hy : F.d * F.c = y.map (quadricMap k).toRingHom)
    (hz : F.d * F.b = z.map (quadricMap k).toRingHom)
    (hnormal : F.map Polynomial.constantCoeff = sourceFrame k) :
    F.map (Polynomial.mapRingHom (fiberCoaction k).toRingHom) =
      Frame.scale (R := (LaurentPolynomial (C k))[X])
        (F.map (Polynomial.mapRingHom (constants k).toRingHom))
        (Units.map (Polynomial.C : LaurentPolynomial (C k) →+*
          (LaurentPolynomial (C k))[X]).toMonoidHom (parameterUnit k)) := by
  apply normalized_frame_scaling_of_base (R := C k) (S := LaurentPolynomial (C k)) F (sourceFrame k)
    (quadricMap k).toRingHom (fiberCoaction k).toRingHom
    (constants k).toRingHom (parameterUnit k) ?_ x y z hx hy hz hnormal
    (sourceFrame_scales k)
  exact congrArg AlgHom.toRingHom (fiberCoaction_quadricMap k)

/-- Every coefficient of the positive/negative frame coordinates has its
prescribed fiber weight.  In particular the infinitesimal coefficients have
weights `1,1,-1,-1`; no weight hypothesis has been placed on the lift itself. -/
theorem normalized_lift_coefficient_weights
    (F : Frame (C k)[X]) (x y z : (BundleCharts.QuadricRing k)[X])
    (hx : F.a * F.b = x.map (quadricMap k).toRingHom)
    (hy : F.d * F.c = y.map (quadricMap k).toRingHom)
    (hz : F.d * F.b = z.map (quadricMap k).toRingHom)
    (hnormal : F.map Polynomial.constantCoeff = sourceFrame k) (n : ℕ) :
    fiberCoaction k (F.a.coeff n) = AddMonoidAlgebra.single 1 (F.a.coeff n) ∧
    fiberCoaction k (F.d.coeff n) = AddMonoidAlgebra.single 1 (F.d.coeff n) ∧
    fiberCoaction k (F.b.coeff n) = AddMonoidAlgebra.single (-1) (F.b.coeff n) ∧
    fiberCoaction k (F.c.coeff n) = AddMonoidAlgebra.single (-1) (F.c.coeff n) := by
  have h := coefficient_scaling (R := C k) (S := LaurentPolynomial (C k)) F (fiberCoaction k).toRingHom
    (constants k).toRingHom (parameterUnit k)
    (normalized_lift_scaling k F x y z hx hy hz hnormal) n
  change fiberCoaction k (F.a.coeff n) = LaurentPolynomial.T 1 * LaurentPolynomial.C (F.a.coeff n) ∧
    fiberCoaction k (F.d.coeff n) = LaurentPolynomial.T 1 * LaurentPolynomial.C (F.d.coeff n) ∧
    fiberCoaction k (F.b.coeff n) = LaurentPolynomial.T (-1) * LaurentPolynomial.C (F.b.coeff n) ∧
    fiberCoaction k (F.c.coeff n) = LaurentPolynomial.T (-1) * LaurentPolynomial.C (F.c.coeff n) at h
  simp only [LaurentPolynomial.single_eq_C_mul_T]
  exact ⟨h.1.trans (mul_comm (LaurentPolynomial.T 1) (LaurentPolynomial.C (F.a.coeff n))),
    h.2.1.trans (mul_comm (LaurentPolynomial.T 1) (LaurentPolynomial.C (F.d.coeff n))),
    h.2.2.1.trans (mul_comm (LaurentPolynomial.T (-1)) (LaurentPolynomial.C (F.b.coeff n))),
    h.2.2.2.trans (mul_comm (LaurentPolynomial.T (-1)) (LaurentPolynomial.C (F.c.coeff n)))⟩

/-- Every polynomial coefficient pulled back from the base quadric is fixed by
fiber scaling. -/
theorem base_polynomial_coefficient_fixed (p : (BundleCharts.QuadricRing k)[X]) (n : ℕ) :
    fiberCoaction k ((p.map (quadricMap k).toRingHom).coeff n) =
      AddMonoidAlgebra.single 0 ((p.map (quadricMap k).toRingHom).coeff n) := by
  rw [Polynomial.coeff_map]
  have h := DFunLike.congr_fun (fiberCoaction_quadricMap k) (p.coeff n)
  change fiberCoaction k (quadricMap k (p.coeff n)) =
    LaurentPolynomial.C (quadricMap k (p.coeff n)) at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    LaurentPolynomial.single_eq_C] using h

/-- An arbitrary normalized polynomial lift of a base polynomial family has
exactly the five source fiber weights, coefficient by coefficient.  In
particular no linearity, group law, or equivariance is assumed of the lift. -/
theorem generator_coefficient_weights_of_normalized_lift
    (φ : C k →ₐ[k] (C k)[X])
    (β : BundleCharts.QuadricRing k →ₐ[k] (BundleCharts.QuadricRing k)[X])
    (hext : ∀ p, φ (quadricMap k p) = (β p).map (quadricMap k).toRingHom)
    (hidentity : ∀ q, (φ q).coeff 0 = q) (i : Fin 5) (n : ℕ) :
    fiberCoaction k ((φ (generator k i)).coeff n) =
      AddMonoidAlgebra.single (Obstruction.fiberWeight i) ((φ (generator k i)).coeff n) := by
  let F : Frame (C k)[X] := (sourceFrame k).map φ.toRingHom
  have hx0 : quadricMap k (BundleCharts.qgen k 0) = a k * b k :=
    BundleCharts.baseMap_qgen k 0
  have hy0 : quadricMap k (BundleCharts.qgen k 1) = d k * c k :=
    BundleCharts.baseMap_qgen k 1
  have hz0 : quadricMap k (BundleCharts.qgen k 2) = d k * b k :=
    BundleCharts.baseMap_qgen k 2
  have hu0 : quadricMap k (BundleCharts.qgen k 3) = u k :=
    BundleCharts.baseMap_qgen k 3
  have hx : F.a * F.b = (β (BundleCharts.qgen k 0)).map (quadricMap k).toRingHom := by
    change φ (a k) * φ (b k) = _
    rw [← map_mul, ← hx0, hext]
  have hy : F.d * F.c = (β (BundleCharts.qgen k 1)).map (quadricMap k).toRingHom := by
    change φ (d k) * φ (c k) = _
    rw [← map_mul, ← hy0, hext]
  have hz : F.d * F.b = (β (BundleCharts.qgen k 2)).map (quadricMap k).toRingHom := by
    change φ (d k) * φ (b k) = _
    rw [← map_mul, ← hz0, hext]
  have hnormal : F.map Polynomial.constantCoeff = sourceFrame k := by
    apply Frame.ext
    · exact hidentity (a k)
    · exact hidentity (d k)
    · exact hidentity (b k)
    · exact hidentity (c k)
  have h := normalized_lift_coefficient_weights k F (β (BundleCharts.qgen k 0))
    (β (BundleCharts.qgen k 1)) (β (BundleCharts.qgen k 2)) hx hy hz hnormal n
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2
  · change fiberCoaction k ((φ (u k)).coeff n) =
      AddMonoidAlgebra.single 0 ((φ (u k)).coeff n)
    rw [← hu0, hext]
    exact base_polynomial_coefficient_fixed k (β (BundleCharts.qgen k 3)) n

end StableCoordinate.DeterminantLiftWeights

end

end OAI
