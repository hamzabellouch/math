import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

namespace OAI

/-!
# The localized graded presentation

This file constructs the actual algebra equivalence
`G[p⁻¹] ≃ₐ[k] (B k)[T;T⁻¹]` from Section 3.  No domain hypothesis is
needed for this explicit coordinate calculation.
-/

namespace StableCoordinate.LaurentPresentation
open MvPolynomial
open StableCoordinate.Obstruction

variable (k : Type*) [CommRing k]

noncomputable def xG : G k := gX k 1 ^ 2 - gX k 2 ^ 2 + gX k 0 * gX k 3
noncomputable def yG : G k := gX k 1 + xG k * (xG k + gX k 2 ^ 2)
noncomputable def zG : G k := gX k 1 * xG k + gX k 0 * gX k 4

private theorem quadric_identity {R : Type*} [CommRing R] (p s u F J : R) :
    let x := s ^ 2 - u ^ 2 + p * F
    let y := s + x * (x + u ^ 2)
    let z := s * x + p * J
    x * y - z * (z + 1) =
      p * (x ^ 2 * F - (1 + 2 * s * x) * J - p * J ^ 2) := by
  dsimp
  ring

 theorem quadricG : xG k * yG k - zG k * (zG k + 1) = 0 := by
  have h : xG k ^ 2 * gX k 3 - (1 + 2 * gX k 1 * xG k) * gX k 4 -
      gX k 0 * gX k 4 ^ 2 = 0 := by
    simpa [gX, Hstar, xP, xG, map_ofNat] using mk_Hstar k
  change (let x := gX k 1 ^ 2 - gX k 2 ^ 2 + gX k 0 * gX k 3
          let y := gX k 1 + x * (x + gX k 2 ^ 2)
          let z := gX k 1 * x + gX k 0 * gX k 4
          x * y - z * (z + 1)) = 0
  rw [quadric_identity]
  change gX k 0 * (xG k ^ 2 * gX k 3 - (1 + 2 * gX k 1 * xG k) * gX k 4 -
      gX k 0 * gX k 4 ^ 2) = 0
  rw [h, mul_zero]

/-- The source's degree-zero quadric algebra maps into its graded presentation. -/
noncomputable def baseMap : B k →ₐ[k] G k :=
  Ideal.Quotient.liftₐ (idealB k) (aeval ![xG k, yG k, zG k, gX k 2]) (by
    change Ideal.span {quadricRelation k} ≤ RingHom.ker
      (aeval ![xG k, yG k, zG k, gX k 2]).toRingHom
    apply Ideal.span_le.mpr
    rintro r (rfl : r = quadricRelation k)
    change (aeval ![xG k, yG k, zG k, gX k 2]) (quadricRelation k) = 0
    simpa [quadricRelation] using quadricG k)

@[simp] theorem baseMap_bX (i : Fin 4) :
    baseMap k (bX k i) = ![xG k, yG k, zG k, gX k 2] i := by
  change (aeval ![xG k, yG k, zG k, gX k 2]) (X i) = _
  simp

@[simp] theorem baseMap_sB : baseMap k (sB k) = gX k 1 := by
  simp [sB, yG]

@[simp] theorem baseMap_f0 : baseMap k (f0 k) = gX k 0 * gX k 3 := by
  simp [f0, xG]
  ring

@[simp] theorem baseMap_g0 : baseMap k (g0 k) = gX k 0 * gX k 4 := by
  simp [g0, zG]

abbrev Laurent := LaurentPolynomial (B k)
abbrev Localized := Localization.Away (gX k 0)

noncomputable def localMap : G k →ₐ[k] Localized k :=
  IsScalarTower.toAlgHom k (G k) (Localized k)

noncomputable def localParameter : (Localized k)ˣ where
  val := localMap k (gX k 0)
  inv := IsLocalization.Away.invSelf (gX k 0)
  val_inv := IsLocalization.Away.mul_invSelf (gX k 0)
  inv_val := by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf (gX k 0)

noncomputable def fromLaurent : Laurent k →ₐ[k] Localized k where
  __ := LaurentPolynomial.eval₂ ((localMap k).comp (baseMap k)).toRingHom (localParameter k)
  commutes' r := by
    change LaurentPolynomial.eval₂ ((localMap k).comp (baseMap k)).toRingHom
      (localParameter k) (algebraMap k (Laurent k) r) = algebraMap k (Localized k) r
    rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C]
    exact ((localMap k).comp (baseMap k)).commutes r

@[simp] theorem fromLaurent_C (r : B k) :
    fromLaurent k (LaurentPolynomial.C r) = localMap k (baseMap k r) :=
  LaurentPolynomial.eval₂_C _ _ r

@[simp] theorem fromLaurent_T (n : ℤ) :
    fromLaurent k (LaurentPolynomial.T n) = ((localParameter k) ^ n).val :=
  LaurentPolynomial.eval₂_T _ _ n

@[simp] theorem fromLaurent_T_one :
    fromLaurent k (LaurentPolynomial.T 1) = localMap k (gX k 0) := by
  simp [localParameter]

@[simp] theorem fromLaurent_T_neg_one :
    fromLaurent k (LaurentPolynomial.T (-1)) = IsLocalization.Away.invSelf (gX k 0) := by
  simp [localParameter]
  rfl

noncomputable def laurentValues : Fin 5 → Laurent k :=
  ![LaurentPolynomial.T 1, LaurentPolynomial.C (sB k), LaurentPolynomial.C (bX k 3),
    LaurentPolynomial.C (f0 k) * LaurentPolynomial.T (-1),
    LaurentPolynomial.C (g0 k) * LaurentPolynomial.T (-1)]

private theorem cancel_T (r : B k) :
    (LaurentPolynomial.T 1 : Laurent k) * (LaurentPolynomial.C r * LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C r := by
  calc
    LaurentPolynomial.T 1 * (LaurentPolynomial.C r * LaurentPolynomial.T (-1)) =
        LaurentPolynomial.C r * (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by ring
    _ = LaurentPolynomial.C r := by rw [← LaurentPolynomial.T_add]; simp

private theorem value_x :
    laurentValues k 1 ^ 2 - laurentValues k 2 ^ 2 +
      laurentValues k 0 * laurentValues k 3 = LaurentPolynomial.C (bX k 0) := by
  change LaurentPolynomial.C (sB k) ^ 2 - LaurentPolynomial.C (bX k 3) ^ 2 +
    LaurentPolynomial.T 1 * (LaurentPolynomial.C (f0 k) * LaurentPolynomial.T (-1)) = _
  rw [cancel_T]
  simp only [f0, map_add, map_sub, map_pow]
  ring

private theorem value_y :
    laurentValues k 1 +
      (LaurentPolynomial.C (bX k 0) : Laurent k) *
        (LaurentPolynomial.C (bX k 0) + laurentValues k 2 ^ 2) =
      LaurentPolynomial.C (bX k 1) := by
  change LaurentPolynomial.C (sB k) + LaurentPolynomial.C (bX k 0) *
    (LaurentPolynomial.C (bX k 0) + LaurentPolynomial.C (bX k 3) ^ 2) = _
  simp only [sB, map_sub, map_mul, map_add, map_pow]
  ring

private theorem value_z :
    laurentValues k 1 * LaurentPolynomial.C (bX k 0) +
      laurentValues k 0 * laurentValues k 4 = LaurentPolynomial.C (bX k 2) := by
  change LaurentPolynomial.C (sB k) * LaurentPolynomial.C (bX k 0) +
    LaurentPolynomial.T 1 * (LaurentPolynomial.C (g0 k) * LaurentPolynomial.T (-1)) = _
  rw [cancel_T]
  simp only [g0, map_sub, map_mul]
  ring

private theorem laurentValues_relation :
    (let x := laurentValues k 1 ^ 2 - laurentValues k 2 ^ 2 +
      laurentValues k 0 * laurentValues k 3
     x ^ 2 * laurentValues k 3 - (1 + 2 * laurentValues k 1 * x) *
       laurentValues k 4 - laurentValues k 0 * laurentValues k 4 ^ 2) = 0 := by
  let e := (let x := laurentValues k 1 ^ 2 - laurentValues k 2 ^ 2 +
      laurentValues k 0 * laurentValues k 3
     x ^ 2 * laurentValues k 3 - (1 + 2 * laurentValues k 1 * x) *
       laurentValues k 4 - laurentValues k 0 * laurentValues k 4 ^ 2)
  have he : laurentValues k 0 * e = 0 := by
    dsimp only [e]
    rw [← quadric_identity (laurentValues k 0) (laurentValues k 1) (laurentValues k 2)
      (laurentValues k 3) (laurentValues k 4)]
    rw [value_x, value_y, value_z]
    have h := congrArg (LaurentPolynomial.C : B k →+* Laurent k) (b_relation k)
    simpa using h
  change e = 0
  calc
    e = LaurentPolynomial.T (-1) * (laurentValues k 0 * e) := by
      change e = LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 * e)
      rw [← mul_assoc, ← LaurentPolynomial.T_add]
      simp
    _ = 0 := by rw [he, mul_zero]

noncomputable def toLaurentBase : G k →ₐ[k] Laurent k :=
  Ideal.Quotient.liftₐ (idealG k) (aeval (laurentValues k)) (by
    change Ideal.span {Hstar k} ≤ RingHom.ker (aeval (laurentValues k)).toRingHom
    apply Ideal.span_le.mpr
    rintro r (rfl : r = Hstar k)
    change (aeval (laurentValues k)) (Hstar k) = 0
    simpa only [Hstar, xP, map_sub, map_add, map_mul, map_pow, map_one,
      map_ofNat, aeval_X] using laurentValues_relation k)

@[simp] theorem toLaurentBase_gX (i : Fin 5) :
    toLaurentBase k (gX k i) = laurentValues k i := by
  change (aeval (laurentValues k)) (X i) = laurentValues k i
  simp

theorem toLaurentBase_parameter_isUnit : IsUnit (toLaurentBase k (gX k 0)) := by
  rw [toLaurentBase_gX]
  exact LaurentPolynomial.isUnit_T (R := B k) 1

noncomputable def toLaurent : Localized k →ₐ[k] Laurent k :=
  IsLocalization.Away.liftAlgHom (A := k) (S := Localized k) (P := Laurent k)
    (gX k 0) (f := toLaurentBase k) (toLaurentBase_parameter_isUnit k)

@[simp] theorem toLaurent_localMap (r : G k) :
    toLaurent k (localMap k r) = toLaurentBase k r :=
  IsLocalization.Away.lift_eq (S := Localized k) (gX k 0)
    (toLaurentBase_parameter_isUnit k) r

@[simp] theorem toLaurentBase_xG :
    toLaurentBase k (xG k) = LaurentPolynomial.C (bX k 0) := by
  simpa only [xG, map_add, map_sub, map_pow, map_mul, toLaurentBase_gX] using value_x k

@[simp] theorem toLaurentBase_yG :
    toLaurentBase k (yG k) = LaurentPolynomial.C (bX k 1) := by
  simpa only [yG, map_add, map_mul, map_pow, toLaurentBase_xG, toLaurentBase_gX]
    using value_y k

@[simp] theorem toLaurentBase_zG :
    toLaurentBase k (zG k) = LaurentPolynomial.C (bX k 2) := by
  simpa only [zG, map_add, map_mul, toLaurentBase_xG, toLaurentBase_gX] using value_z k

 theorem toLaurentBase_comp_baseMap :
    (toLaurentBase k).comp (baseMap k) =
      IsScalarTower.toAlgHom k (B k) (Laurent k) := by
  apply Ideal.Quotient.algHom_ext k
  apply MvPolynomial.algHom_ext
  intro i
  change toLaurentBase k (baseMap k (bX k i)) = LaurentPolynomial.C (bX k i)
  fin_cases i <;> simp [laurentValues]

@[simp] theorem toLaurentBase_baseMap (r : B k) :
    toLaurentBase k (baseMap k r) = LaurentPolynomial.C r :=
  DFunLike.congr_fun (toLaurentBase_comp_baseMap k) r

private theorem parameter_cancel (r : Localized k) :
    (localMap k (gX k 0) * r) * IsLocalization.Away.invSelf (gX k 0) = r := by
  calc
    (localMap k (gX k 0) * r) * IsLocalization.Away.invSelf (gX k 0) =
        r * (localMap k (gX k 0) * IsLocalization.Away.invSelf (gX k 0)) := by ring
    _ = r := by rw [show localMap k (gX k 0) * IsLocalization.Away.invSelf (gX k 0) = 1 from
        IsLocalization.Away.mul_invSelf (gX k 0), mul_one]

 theorem fromLaurent_comp_toLaurentBase :
    (fromLaurent k).comp (toLaurentBase k) = localMap k := by
  apply Ideal.Quotient.algHom_ext k
  apply MvPolynomial.algHom_ext
  intro i
  change fromLaurent k (toLaurentBase k (gX k i)) = localMap k (gX k i)
  fin_cases i
  · simp [laurentValues, localParameter]
  · simp [laurentValues]
  · simp [laurentValues]
  · simp only [toLaurentBase_gX]
    change fromLaurent k (LaurentPolynomial.C (f0 k) * LaurentPolynomial.T (-1)) = _
    rw [map_mul, fromLaurent_C, fromLaurent_T_neg_one, baseMap_f0, map_mul, parameter_cancel]
    rfl
  · simp only [toLaurentBase_gX]
    change fromLaurent k (LaurentPolynomial.C (g0 k) * LaurentPolynomial.T (-1)) = _
    rw [map_mul, fromLaurent_C, fromLaurent_T_neg_one, baseMap_g0, map_mul, parameter_cancel]
    rfl

@[simp] theorem fromLaurent_toLaurentBase (r : G k) :
    fromLaurent k (toLaurentBase k r) = localMap k r :=
  DFunLike.congr_fun (fromLaurent_comp_toLaurentBase k) r

@[simp] theorem toLaurent_invSelf :
    toLaurent k (IsLocalization.Away.invSelf (gX k 0)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (toLaurent k) (IsLocalization.Away.mul_invSelf
    (S := Localized k) (gX k 0))
  change toLaurent k (localMap k (gX k 0) * IsLocalization.Away.invSelf (gX k 0)) =
    toLaurent k 1 at h
  simp only [map_mul, map_one, toLaurent_localMap, toLaurentBase_gX] at h
  change LaurentPolynomial.T 1 * toLaurent k (IsLocalization.Away.invSelf (gX k 0)) = 1 at h
  calc
    toLaurent k (IsLocalization.Away.invSelf (gX k 0)) =
        LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 *
          toLaurent k (IsLocalization.Away.invSelf (gX k 0))) := by
      rw [← mul_assoc, ← LaurentPolynomial.T_add]
      simp
    _ = LaurentPolynomial.T (-1) := by rw [h, mul_one]

private theorem laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1))
    (hTi : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1))) : f = g := by
  apply RingHom.ext
  intro r
  refine LaurentPolynomial.induction_on r hC ?_ ?_ ?_
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro n a h
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul f, map_mul g, h, hT]
  · intro n a h
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul f, map_mul g, h, hTi]

 theorem toLaurent_comp_fromLaurent :
    (toLaurent k).comp (fromLaurent k) = AlgHom.id k (Laurent k) := by
  apply AlgHom.coe_ringHom_injective
  apply laurent_hom_ext (R := B k) (S := Laurent k)
  · intro r
    change toLaurent k (fromLaurent k (LaurentPolynomial.C r)) = LaurentPolynomial.C r
    simp
  · change toLaurent k (fromLaurent k (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
    rw [fromLaurent_T_one, toLaurent_localMap, toLaurentBase_gX]
    rfl
  · change toLaurent k (fromLaurent k (LaurentPolynomial.T (-1))) = LaurentPolynomial.T (-1)
    rw [fromLaurent_T_neg_one, toLaurent_invSelf]

 theorem fromLaurent_comp_toLaurent :
    (fromLaurent k).comp (toLaurent k) = AlgHom.id k (Localized k) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (gX k 0))
  apply RingHom.ext
  intro r
  change fromLaurent k (toLaurent k (localMap k r)) = localMap k r
  simp

/-- The exact Laurent presentation of the localized graded hypersurface. -/
noncomputable def equiv : Localized k ≃ₐ[k] Laurent k :=
  AlgEquiv.ofAlgHom (toLaurent k) (fromLaurent k)
    (toLaurent_comp_fromLaurent k) (fromLaurent_comp_toLaurent k)

@[simp] theorem equiv_apply (r : Localized k) : equiv k r = toLaurent k r := rfl
@[simp] theorem equiv_symm_apply (r : Laurent k) : (equiv k).symm r = fromLaurent k r := rfl

/-- Every source generator has the required explicit Laurent image. -/
@[simp] theorem equiv_localMap_gX (i : Fin 5) :
    equiv k (localMap k (gX k i)) = laurentValues k i := by simp

/-- The quadric subalgebra becomes precisely the constant Laurent polynomials. -/
@[simp] theorem equiv_localMap_baseMap (r : B k) :
    equiv k (localMap k (baseMap k r)) = LaurentPolynomial.C r := by simp

/-- Injectivity of the degree-zero quadric map follows from its constant Laurent image. -/
theorem baseMap_injective : Function.Injective (baseMap k) := by
  intro a b h
  have hc : LaurentPolynomial.C a = (LaurentPolynomial.C b : Laurent k) := by
    simpa using congrArg (fun r => equiv k (localMap k r)) h
  have he := congrArg (fun p : Laurent k => p.coeff 0) hc
  simpa using he

end StableCoordinate.LaurentPresentation

end OAI
