import OAI.AlgebraicGeometry.StableCoordinate.DeterminantRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# Explicit affine charts for the determinant ring

These are the `a`- and `d`-localizations in Section 5, not the bundle charts
in Section 4. The coefficient algebra has independent variables `a,d,u`.
-/

namespace StableCoordinate.DeterminantRing

open MvPolynomial

variable (k : Type*) [CommRing k]

abbrev BaseAway (i : Fin 3) := Localization.Away (X i : Base k)
abbrev Chart (i : Fin 3) := Polynomial (BaseAway k i)
abbrev AwayA := Localization.Away (a k)
abbrev AwayD := Localization.Away (d k)

noncomputable def chartVariable (i j : Fin 3) : Chart k i :=
  Polynomial.C (algebraMap (Base k) (BaseAway k i) (X j))
noncomputable def chartInverse (i : Fin 3) : Chart k i :=
  Polynomial.C (IsLocalization.Away.invSelf (X i : Base k))

@[simp] theorem chartVariable_mul_inverse (i : Fin 3) :
    chartVariable k i i * chartInverse k i = 1 := by
  rw [chartVariable, chartInverse, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

theorem chartVariable_isUnit (i : Fin 3) : IsUnit (chartVariable k i i) :=
  isUnit_iff_exists_inv.mpr ⟨chartInverse k i, chartVariable_mul_inverse k i⟩

noncomputable def chartMapA : C k →ₐ[k] Chart k 0 :=
  lift (chartVariable k 0 0) (chartVariable k 0 1) Polynomial.X
    (chartInverse k 0 * (1 + Polynomial.X * chartVariable k 0 1))
    (chartVariable k 0 2) (by
      calc
        _ = (chartVariable k 0 0 * chartInverse k 0) *
            (1 + Polynomial.X * chartVariable k 0 1) -
            Polynomial.X * chartVariable k 0 1 := by ring
        _ = 1 := by rw [chartVariable_mul_inverse]; ring)

@[simp] theorem chartMapA_a : chartMapA k (a k) = chartVariable k 0 0 := by
  simp [chartMapA]
@[simp] theorem chartMapA_d : chartMapA k (d k) = chartVariable k 0 1 := by
  simp [chartMapA]
@[simp] theorem chartMapA_b : chartMapA k (b k) = Polynomial.X := by
  simp [chartMapA]
@[simp] theorem chartMapA_c : chartMapA k (c k) =
    chartInverse k 0 * (1 + Polynomial.X * chartVariable k 0 1) := by
  simp [chartMapA]
@[simp] theorem chartMapA_u : chartMapA k (u k) = chartVariable k 0 2 := by
  simp [chartMapA]

noncomputable def toChartA : AwayA k →ₐ[k] Chart k 0 :=
  IsLocalization.Away.liftAlgHom (a k)
    (show IsUnit (chartMapA k (a k)) by rw [chartMapA_a]; exact chartVariable_isUnit k 0)

@[simp] theorem toChartA_algebraMap (r : C k) :
    toChartA k (algebraMap (C k) (AwayA k) r) = chartMapA k r := by
  simp [toChartA, IsLocalization.Away.liftAlgHom_apply]

noncomputable def baseToAwayA : Base k →ₐ[k] AwayA k :=
  (Algebra.algHom k (C k) (AwayA k)).comp baseMap

@[simp] theorem baseToAwayA_X0 : baseToAwayA k (X 0) =
    algebraMap (C k) (AwayA k) (a k) := by simp [baseToAwayA, Algebra.algHom]
@[simp] theorem baseToAwayA_X1 : baseToAwayA k (X 1) =
    algebraMap (C k) (AwayA k) (d k) := by simp [baseToAwayA, Algebra.algHom]
@[simp] theorem baseToAwayA_X2 : baseToAwayA k (X 2) =
    algebraMap (C k) (AwayA k) (u k) := by simp [baseToAwayA, Algebra.algHom]

noncomputable def coefficientFromChartA : BaseAway k 0 →ₐ[k] AwayA k :=
  IsLocalization.Away.liftAlgHom (X 0 : Base k)
    (show IsUnit (baseToAwayA k (X 0)) by
      rw [baseToAwayA_X0]
      exact IsLocalization.Away.algebraMap_isUnit (a k))

@[simp] theorem coefficientFromChartA_algebraMap (r : Base k) :
    coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) r) = baseToAwayA k r := by
  simp [coefficientFromChartA, IsLocalization.Away.liftAlgHom_apply]

noncomputable def fromChartA : Chart k 0 →ₐ[k] AwayA k :=
  Polynomial.aevalTower (coefficientFromChartA k) (algebraMap (C k) (AwayA k) (b k))

@[simp] theorem fromChartA_X : fromChartA k Polynomial.X =
    algebraMap (C k) (AwayA k) (b k) := by simp [fromChartA]
@[simp] theorem fromChartA_C (r : BaseAway k 0) :
    fromChartA k (Polynomial.C r) = coefficientFromChartA k r := by simp [fromChartA]
@[simp] theorem fromChartA_variable (i : Fin 3) :
    fromChartA k (chartVariable k 0 i) = baseToAwayA k (X i) := by
  simp [chartVariable]

private theorem map_invSelf_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] (r : R) [IsLocalization.Away r S] (f : S →+* T) (y : T)
    (hy : f (algebraMap R S r) * y = 1) :
    f (IsLocalization.Away.invSelf r) = y := by
  apply ((IsLocalization.Away.algebraMap_isUnit r).map f).mul_left_cancel
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one, hy]

@[simp] theorem fromChartA_inverse :
    fromChartA k (chartInverse k 0) = IsLocalization.Away.invSelf (a k) := by
  rw [chartInverse, fromChartA_C]
  apply map_invSelf_eq (X 0 : Base k) (coefficientFromChartA k).toRingHom
  change coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) (X 0)) *
    IsLocalization.Away.invSelf (a k) = 1
  simp

@[simp] theorem toChartA_inverse :
    toChartA k (IsLocalization.Away.invSelf (a k)) = chartInverse k 0 := by
  apply map_invSelf_eq (a k) (toChartA k).toRingHom
  change toChartA k (algebraMap (C k) (AwayA k) (a k)) * chartInverse k 0 = 1
  simp

theorem localized_c : algebraMap (C k) (AwayA k) (c k) =
    IsLocalization.Away.invSelf (a k) *
      (1 + algebraMap (C k) (AwayA k) (b k) * algebraMap (C k) (AwayA k) (d k)) := by
  apply (IsLocalization.Away.algebraMap_isUnit (a k)).mul_left_cancel
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have h := congrArg (algebraMap (C k) (AwayA k)) (determinant_relation k)
  simp only [map_sub, map_mul, map_one] at h
  linear_combination h

theorem fromChartA_comp_toChartA :
    (fromChartA k).comp (toChartA k) = AlgHom.id k (AwayA k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (a k))
  apply hom_ext <;> simp [Algebra.algHom, localized_c]

theorem toChartA_comp_fromChartA :
    (toChartA k).comp (fromChartA k) = AlgHom.id k (Chart k 0) := by
  apply Polynomial.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X 0 : Base k))
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [Algebra.algHom, chartVariable]
  · simp

/-- The actual algebra equivalence `C[a⁻¹] ≃ k[a,a⁻¹,d,u][b]`. -/
noncomputable def chartEquivA : AwayA k ≃ₐ[k] Chart k 0 :=
  AlgEquiv.ofAlgHom (toChartA k) (fromChartA k)
    (toChartA_comp_fromChartA k) (fromChartA_comp_toChartA k)

noncomputable def chartMapD : C k →ₐ[k] Chart k 1 :=
  lift (chartVariable k 1 0) (chartVariable k 1 1)
    (chartInverse k 1 * (chartVariable k 1 0 * Polynomial.X - 1))
    Polynomial.X (chartVariable k 1 2) (by
      calc
        _ = chartVariable k 1 0 * Polynomial.X -
            (chartVariable k 1 1 * chartInverse k 1) *
            (chartVariable k 1 0 * Polynomial.X - 1) := by ring
        _ = 1 := by rw [chartVariable_mul_inverse]; ring)

@[simp] theorem chartMapD_a : chartMapD k (a k) = chartVariable k 1 0 := by
  simp [chartMapD]
@[simp] theorem chartMapD_d : chartMapD k (d k) = chartVariable k 1 1 := by
  simp [chartMapD]
@[simp] theorem chartMapD_b : chartMapD k (b k) =
    chartInverse k 1 * (chartVariable k 1 0 * Polynomial.X - 1) := by
  simp [chartMapD]
@[simp] theorem chartMapD_c : chartMapD k (c k) = Polynomial.X := by
  simp [chartMapD]
@[simp] theorem chartMapD_u : chartMapD k (u k) = chartVariable k 1 2 := by
  simp [chartMapD]

noncomputable def toChartD : AwayD k →ₐ[k] Chart k 1 :=
  IsLocalization.Away.liftAlgHom (d k)
    (show IsUnit (chartMapD k (d k)) by rw [chartMapD_d]; exact chartVariable_isUnit k 1)

@[simp] theorem toChartD_algebraMap (r : C k) :
    toChartD k (algebraMap (C k) (AwayD k) r) = chartMapD k r := by
  simp [toChartD, IsLocalization.Away.liftAlgHom_apply]

noncomputable def baseToAwayD : Base k →ₐ[k] AwayD k :=
  (Algebra.algHom k (C k) (AwayD k)).comp baseMap

@[simp] theorem baseToAwayD_X0 : baseToAwayD k (X 0) =
    algebraMap (C k) (AwayD k) (a k) := by simp [baseToAwayD, Algebra.algHom]
@[simp] theorem baseToAwayD_X1 : baseToAwayD k (X 1) =
    algebraMap (C k) (AwayD k) (d k) := by simp [baseToAwayD, Algebra.algHom]
@[simp] theorem baseToAwayD_X2 : baseToAwayD k (X 2) =
    algebraMap (C k) (AwayD k) (u k) := by simp [baseToAwayD, Algebra.algHom]

noncomputable def coefficientFromChartD : BaseAway k 1 →ₐ[k] AwayD k :=
  IsLocalization.Away.liftAlgHom (X 1 : Base k)
    (show IsUnit (baseToAwayD k (X 1)) by
      rw [baseToAwayD_X1]
      exact IsLocalization.Away.algebraMap_isUnit (d k))

@[simp] theorem coefficientFromChartD_algebraMap (r : Base k) :
    coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) r) = baseToAwayD k r := by
  simp [coefficientFromChartD, IsLocalization.Away.liftAlgHom_apply]

noncomputable def fromChartD : Chart k 1 →ₐ[k] AwayD k :=
  Polynomial.aevalTower (coefficientFromChartD k) (algebraMap (C k) (AwayD k) (c k))

@[simp] theorem fromChartD_X : fromChartD k Polynomial.X =
    algebraMap (C k) (AwayD k) (c k) := by simp [fromChartD]
@[simp] theorem fromChartD_C (r : BaseAway k 1) :
    fromChartD k (Polynomial.C r) = coefficientFromChartD k r := by simp [fromChartD]
@[simp] theorem fromChartD_variable (i : Fin 3) :
    fromChartD k (chartVariable k 1 i) = baseToAwayD k (X i) := by
  simp [chartVariable]

@[simp] theorem fromChartD_inverse :
    fromChartD k (chartInverse k 1) = IsLocalization.Away.invSelf (d k) := by
  rw [chartInverse, fromChartD_C]
  apply map_invSelf_eq (X 1 : Base k) (coefficientFromChartD k).toRingHom
  change coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) (X 1)) *
    IsLocalization.Away.invSelf (d k) = 1
  simp

@[simp] theorem toChartD_inverse :
    toChartD k (IsLocalization.Away.invSelf (d k)) = chartInverse k 1 := by
  apply map_invSelf_eq (d k) (toChartD k).toRingHom
  change toChartD k (algebraMap (C k) (AwayD k) (d k)) * chartInverse k 1 = 1
  simp

theorem localized_b : algebraMap (C k) (AwayD k) (b k) =
    IsLocalization.Away.invSelf (d k) *
      (algebraMap (C k) (AwayD k) (a k) * algebraMap (C k) (AwayD k) (c k) - 1) := by
  apply (IsLocalization.Away.algebraMap_isUnit (d k)).mul_left_cancel
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have h := congrArg (algebraMap (C k) (AwayD k)) (determinant_relation k)
  simp only [map_sub, map_mul, map_one] at h
  linear_combination -h

theorem fromChartD_comp_toChartD :
    (fromChartD k).comp (toChartD k) = AlgHom.id k (AwayD k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (d k))
  apply hom_ext <;> simp [Algebra.algHom, localized_b]

theorem toChartD_comp_fromChartD :
    (toChartD k).comp (fromChartD k) = AlgHom.id k (Chart k 1) := by
  apply Polynomial.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X 1 : Base k))
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [Algebra.algHom, chartVariable]
  · simp

/-- The actual algebra equivalence `C[d⁻¹] ≃ k[a,d,d⁻¹,u][c]`. -/
noncomputable def chartEquivD : AwayD k ≃ₐ[k] Chart k 1 :=
  AlgEquiv.ofAlgHom (toChartD k) (fromChartD k)
    (toChartD_comp_fromChartD k) (fromChartD_comp_toChartD k)

theorem chartMapA_comp_baseMap :
    (chartMapA k).comp baseMap =
      (Polynomial.CAlgHom : BaseAway k 0 →ₐ[k] Chart k 0).comp
        (Algebra.algHom k (Base k) (BaseAway k 0)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap, chartVariable, Algebra.algHom]

theorem chartMapD_comp_baseMap :
    (chartMapD k).comp baseMap =
      (Polynomial.CAlgHom : BaseAway k 1 →ₐ[k] Chart k 1).comp
        (Algebra.algHom k (Base k) (BaseAway k 1)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap, chartVariable, Algebra.algHom]

@[simp] theorem chartMapA_baseMap (r : Base k) :
    chartMapA k (baseMap r) = Polynomial.C (algebraMap (Base k) (BaseAway k 0) r) := by
  exact AlgHom.congr_fun (chartMapA_comp_baseMap k) r

@[simp] theorem chartMapD_baseMap (r : Base k) :
    chartMapD k (baseMap r) = Polynomial.C (algebraMap (Base k) (BaseAway k 1) r) := by
  exact AlgHom.congr_fun (chartMapD_comp_baseMap k) r

/-- Algebraic independence of `a,d,u` in the determinant quotient. -/
theorem baseMap_injective [IsDomain k] : Function.Injective (baseMap (k := k)) := by
  intro r s h
  have h' := congrArg (chartMapA k) h
  simp only [chartMapA_baseMap] at h'
  apply IsLocalization.injective (BaseAway k 0)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin 3)))
  exact Polynomial.C_injective h'

/-- Compatibility with the actual polynomial coefficient algebra. -/
noncomputable def chartMapAOverBase : C k →ₐ[Base k] Chart k 0 where
  __ := (chartMapA k).toRingHom
  commutes' r := chartMapA_baseMap k r

/-- Compatibility with the actual polynomial coefficient algebra. -/
noncomputable def chartMapDOverBase : C k →ₐ[Base k] Chart k 1 where
  __ := (chartMapD k).toRingHom
  commutes' r := chartMapD_baseMap k r

noncomputable instance coefficientAlgebraA : Algebra (BaseAway k 0) (AwayA k) :=
  (coefficientFromChartA k).toRingHom.toAlgebra
noncomputable instance coefficientAlgebraD : Algebra (BaseAway k 1) (AwayD k) :=
  (coefficientFromChartD k).toRingHom.toAlgebra

instance coefficientScalarTowerA : IsScalarTower k (BaseAway k 0) (AwayA k) :=
  IsScalarTower.of_algHom (coefficientFromChartA k)
instance coefficientScalarTowerD : IsScalarTower k (BaseAway k 1) (AwayD k) :=
  IsScalarTower.of_algHom (coefficientFromChartD k)

instance baseCoefficientScalarTowerA : IsScalarTower (Base k) (BaseAway k 0) (AwayA k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap (Base k) (AwayA k) r =
    coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) r)
  rw [coefficientFromChartA_algebraMap]
  rfl

instance baseCoefficientScalarTowerD : IsScalarTower (Base k) (BaseAway k 1) (AwayD k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap (Base k) (AwayD k) r =
    coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) r)
  rw [coefficientFromChartD_algebraMap]
  rfl

/-- The a-chart equivalence, over its full localized coefficient ring. -/
noncomputable def chartEquivAOverCoefficients : AwayA k ≃ₐ[BaseAway k 0] Chart k 0 where
  __ := (chartEquivA k).toRingEquiv
  commutes' r := by
    change toChartA k (coefficientFromChartA k r) = Polynomial.C r
    have h := AlgHom.congr_fun (toChartA_comp_fromChartA k) (Polynomial.C r)
    simpa using h

/-- The d-chart equivalence, over its full localized coefficient ring. -/
noncomputable def chartEquivDOverCoefficients : AwayD k ≃ₐ[BaseAway k 1] Chart k 1 where
  __ := (chartEquivD k).toRingEquiv
  commutes' r := by
    change toChartD k (coefficientFromChartD k r) = Polynomial.C r
    have h := AlgHom.congr_fun (toChartD_comp_fromChartD k) (Polynomial.C r)
    simpa using h

/-- Chart injectivity follows from the domain property, not an assumed chart inclusion. -/
theorem chartMapA_injective [IsDomain k] [IsDomain (C k)] :
    Function.Injective (chartMapA k) := by
  have ha : a k ≠ 0 := by
    intro h
    apply MvPolynomial.X_ne_zero (0 : Fin 3) (R := k)
    apply baseMap_injective k
    simpa using h
  intro r s h
  apply IsLocalization.injective (AwayA k) (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  apply (chartEquivA k).injective
  change toChartA k _ = toChartA k _
  simpa using h

/-- Chart injectivity follows from the domain property, not an assumed chart inclusion. -/
theorem chartMapD_injective [IsDomain k] [IsDomain (C k)] :
    Function.Injective (chartMapD k) := by
  have hd : d k ≠ 0 := by
    intro h
    apply MvPolynomial.X_ne_zero (1 : Fin 3) (R := k)
    apply baseMap_injective k
    simpa using h
  intro r s h
  apply IsLocalization.injective (AwayD k) (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  apply (chartEquivD k).injective
  change toChartD k _ = toChartD k _
  simpa using h

end StableCoordinate.DeterminantRing

end OAI
