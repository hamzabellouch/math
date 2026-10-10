import Mathlib

namespace OAI

/-!
# Algebra of the two charts of the determinant bundle

This module formalizes the quadric-to-determinant-ring map in Section 4 of the source.
All variables are independent before taking the displayed principal-ideal quotient.
The chosen sections over `D(z+1)` and `D(z)` prove the base map injective without
assuming that the quadric ring is a domain.
-/

noncomputable section

namespace StableCoordinate.BundleCharts

open MvPolynomial

variable (K : Type*) [CommRing K]

/-- Defining ideal of the quadric with independent coordinates `(x,y,z,u)`. -/
def quadricIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span {X 0 * X 1 - X 2 * (X 2 + 1)}

/-- Coordinate ring of the quadric times the affine `u`-line. -/
abbrev QuadricRing := MvPolynomial (Fin 4) K ⧸ quadricIdeal K

/-- Defining ideal of the determinant-one ring with coordinates `(a,d,b,c,u)`. -/
def determinantIdeal : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span {X 0 * X 3 - X 2 * X 1 - 1}

/-- Coordinate ring of `SL₂ × A¹`, in the source's coordinate order. -/
abbrev DeterminantRing := MvPolynomial (Fin 5) K ⧸ determinantIdeal K

/-- The four quotient generators `(x,y,z,u)`. -/
def qgen (i : Fin 4) : QuadricRing K := Ideal.Quotient.mk _ (X i)

/-- The five quotient generators `(a,d,b,c,u)`. -/
def dgen (i : Fin 5) : DeterminantRing K := Ideal.Quotient.mk _ (X i)

theorem quadric_relation : qgen K 0 * qgen K 1 = qgen K 2 * (qgen K 2 + 1) := by
  apply sub_eq_zero.mp
  have h : Ideal.Quotient.mk (quadricIdeal K)
      (X 0 * X 1 - X 2 * (X 2 + 1) : MvPolynomial (Fin 4) K) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_sub, map_mul, map_add, map_one, qgen] using h

theorem determinant_relation : dgen K 0 * dgen K 3 - dgen K 2 * dgen K 1 = 1 := by
  apply sub_eq_zero.mp
  have h : Ideal.Quotient.mk (determinantIdeal K)
      (X 0 * X 3 - X 2 * X 1 - 1 : MvPolynomial (Fin 5) K) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_sub, map_mul, map_one, dgen] using h

/-- The map of polynomial rings underlying `x=ab, y=dc, z=db, u=u`. -/
def basePolynomialMap : MvPolynomial (Fin 4) K →ₐ[K] DeterminantRing K :=
  MvPolynomial.aeval ![dgen K 0 * dgen K 2, dgen K 1 * dgen K 3,
    dgen K 1 * dgen K 2, dgen K 4]

theorem quadricIdeal_le_ker_basePolynomialMap :
    quadricIdeal K ≤ RingHom.ker (basePolynomialMap K).toRingHom := by
  rw [quadricIdeal, Ideal.span_singleton_le_iff_mem]
  change basePolynomialMap K (X 0 * X 1 - X 2 * (X 2 + 1)) = 0
  simp only [basePolynomialMap, map_mul, map_sub, map_add, map_one, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have h := determinant_relation K
  linear_combination (dgen K 1 * dgen K 2) * h

/-- The source's quadric-to-determinant-ring map. -/
def baseMap : QuadricRing K →ₐ[K] DeterminantRing K :=
  Ideal.Quotient.liftₐ (quadricIdeal K) (basePolynomialMap K)
    (fun _ h => quadricIdeal_le_ker_basePolynomialMap K h)

@[simp] theorem baseMap_qgen (i : Fin 4) :
    baseMap K (qgen K i) =
      ![dgen K 0 * dgen K 2, dgen K 1 * dgen K 3,
        dgen K 1 * dgen K 2, dgen K 4] i := by
  change basePolynomialMap K (X i) = _
  simp [basePolynomialMap]

/-- The base chart `D(z+1)`. -/
abbrev ChartA := Localization.Away (qgen K 2 + 1)

/-- The base chart `D(z)`. -/
abbrev ChartD := Localization.Away (qgen K 2)

/-- Base-chart coordinate functions. -/
def agen (i : Fin 4) : ChartA K := algebraMap (QuadricRing K) _ (qgen K i)

/-- Base-chart coordinate functions. -/
def zgen (i : Fin 4) : ChartD K := algebraMap (QuadricRing K) _ (qgen K i)

/-- Inverse of `z+1` on the first chart. -/
def ainv : ChartA K := IsLocalization.Away.invSelf (qgen K 2 + 1)

/-- Inverse of `z` on the second chart. -/
def zinv : ChartD K := IsLocalization.Away.invSelf (qgen K 2)

theorem agen_relation : agen K 0 * agen K 1 = agen K 2 * (agen K 2 + 1) := by
  simpa only [map_mul, map_add, map_one, agen] using
    congrArg (algebraMap (QuadricRing K) (ChartA K)) (quadric_relation K)

theorem zgen_relation : zgen K 0 * zgen K 1 = zgen K 2 * (zgen K 2 + 1) := by
  simpa only [map_mul, map_add, map_one, zgen] using
    congrArg (algebraMap (QuadricRing K) (ChartD K)) (quadric_relation K)

@[simp] theorem agen_mul_ainv : (agen K 2 + 1) * ainv K = 1 := by
  simpa only [agen, ainv, map_add, map_one] using
    IsLocalization.Away.mul_invSelf (qgen K 2 + 1) (S := ChartA K)

@[simp] theorem zgen_mul_zinv : zgen K 2 * zinv K = 1 := by
  exact IsLocalization.Away.mul_invSelf (qgen K 2) (S := ChartD K)

/-- The section with `a=1` over `D(z+1)`, expressed on polynomial generators. -/
def sectionAPolynomialMap : MvPolynomial (Fin 5) K →ₐ[K] ChartA K :=
  MvPolynomial.aeval ![1, agen K 1 * ainv K, agen K 0, agen K 2 + 1, agen K 3]

/-- The section with `d=1` over `D(z)`, expressed on polynomial generators. -/
def sectionDPolynomialMap : MvPolynomial (Fin 5) K →ₐ[K] ChartD K :=
  MvPolynomial.aeval ![zgen K 0 * zinv K, 1, zgen K 2, zgen K 1, zgen K 3]

theorem determinantIdeal_le_ker_sectionAPolynomialMap :
    determinantIdeal K ≤ RingHom.ker (sectionAPolynomialMap K).toRingHom := by
  rw [determinantIdeal, Ideal.span_singleton_le_iff_mem]
  change sectionAPolynomialMap K (X 0 * X 3 - X 2 * X 1 - 1) = 0
  simp only [sectionAPolynomialMap, map_mul, map_sub, map_one,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  have hr := agen_relation K
  have hi := agen_mul_ainv K
  linear_combination -(ainv K) * hr - (agen K 2) * hi

theorem determinantIdeal_le_ker_sectionDPolynomialMap :
    determinantIdeal K ≤ RingHom.ker (sectionDPolynomialMap K).toRingHom := by
  rw [determinantIdeal, Ideal.span_singleton_le_iff_mem]
  change sectionDPolynomialMap K (X 0 * X 3 - X 2 * X 1 - 1) = 0
  simp only [sectionDPolynomialMap, map_mul, map_sub, map_one,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  have hr := zgen_relation K
  have hi := zgen_mul_zinv K
  linear_combination (zinv K) * hr + (zgen K 2 + 1) * hi

/-- Restriction to the section `a=1` of the determinant bundle on the first base chart. -/
def sectionA : DeterminantRing K →ₐ[K] ChartA K :=
  Ideal.Quotient.liftₐ (determinantIdeal K) (sectionAPolynomialMap K)
    (fun _ h => determinantIdeal_le_ker_sectionAPolynomialMap K h)

/-- Restriction to the section `d=1` of the determinant bundle on the second base chart. -/
def sectionD : DeterminantRing K →ₐ[K] ChartD K :=
  Ideal.Quotient.liftₐ (determinantIdeal K) (sectionDPolynomialMap K)
    (fun _ h => determinantIdeal_le_ker_sectionDPolynomialMap K h)

@[simp] theorem sectionA_dgen (i : Fin 5) :
    sectionA K (dgen K i) =
      ![1, agen K 1 * ainv K, agen K 0, agen K 2 + 1, agen K 3] i := by
  change sectionAPolynomialMap K (X i) = _
  simp [sectionAPolynomialMap]

@[simp] theorem sectionD_dgen (i : Fin 5) :
    sectionD K (dgen K i) =
      ![zgen K 0 * zinv K, 1, zgen K 2, zgen K 1, zgen K 3] i := by
  change sectionDPolynomialMap K (X i) = _
  simp [sectionDPolynomialMap]

theorem sectionA_y :
    (agen K 1 * ainv K) * (agen K 2 + 1) = agen K 1 := by
  linear_combination (agen K 1) * (agen_mul_ainv K)

theorem sectionA_z : (agen K 1 * ainv K) * agen K 0 = agen K 2 := by
  linear_combination (ainv K) * (agen_relation K) + (agen K 2) * (agen_mul_ainv K)

theorem sectionD_x : (zgen K 0 * zinv K) * zgen K 2 = zgen K 0 := by
  linear_combination (zgen K 0) * (zgen_mul_zinv K)

/-- The first local section splits the base map after localization. -/
theorem sectionA_comp_baseMap :
    (sectionA K).comp (baseMap K) = IsScalarTower.toAlgHom K (QuadricRing K) (ChartA K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change sectionA K (baseMap K (qgen K i)) = agen K i
  fin_cases i <;> simp [sectionA_y, sectionA_z]

/-- The second local section splits the base map after localization. -/
theorem sectionD_comp_baseMap :
    (sectionD K).comp (baseMap K) = IsScalarTower.toAlgHom K (QuadricRing K) (ChartD K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change sectionD K (baseMap K (qgen K i)) = zgen K i
  fin_cases i <;> simp [sectionD_x]

@[simp] theorem sectionA_baseMap (p : QuadricRing K) :
    sectionA K (baseMap K p) = algebraMap (QuadricRing K) (ChartA K) p :=
  AlgHom.congr_fun (sectionA_comp_baseMap K) p

@[simp] theorem sectionD_baseMap (p : QuadricRing K) :
    sectionD K (baseMap K p) = algebraMap (QuadricRing K) (ChartD K) p :=
  AlgHom.congr_fun (sectionD_comp_baseMap K) p

/-- The two principal opens cover the base: vanishing on both localizations forces zero.
This argument works over an arbitrary commutative coefficient ring, without a domain assumption. -/
theorem eq_zero_of_chartA_eq_zero_of_chartD_eq_zero (p : QuadricRing K)
    (hA : algebraMap (QuadricRing K) (ChartA K) p = 0)
    (hD : algebraMap (QuadricRing K) (ChartD K) p = 0) : p = 0 := by
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq
    (x := qgen K 2 + 1) (S := ChartA K) (a := p) (b := 0) (by simpa only [map_zero] using hA)
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq
    (x := qgen K 2) (S := ChartD K) (a := p) (b := 0) (by simpa only [map_zero] using hD)
  simp only [mul_zero] at hn hm
  have hcop : IsCoprime (qgen K 2 + 1) (qgen K 2) :=
    IsCoprime.add_one_left_of_dvd (dvd_refl _)
  obtain ⟨s, t, hst⟩ := hcop.pow (m := n) (n := m)
  calc
    p = (s * (qgen K 2 + 1) ^ n + t * qgen K 2 ^ m) * p := by rw [hst, one_mul]
    _ = s * ((qgen K 2 + 1) ^ n * p) + t * (qgen K 2 ^ m * p) := by ring
    _ = 0 := by rw [hn, hm]; ring

/-- The base map has zero kernel, proved using the two explicit local sections. -/
theorem baseMap_eq_zero (p : QuadricRing K) (hp : baseMap K p = 0) : p = 0 := by
  apply eq_zero_of_chartA_eq_zero_of_chartD_eq_zero K p
  · simpa only [sectionA_baseMap, map_zero] using congrArg (sectionA K) hp
  · simpa only [sectionD_baseMap, map_zero] using congrArg (sectionD K) hp

/-- The quadric-to-determinant-ring map of Section 4 is injective. -/
theorem baseMap_injective : Function.Injective (baseMap K) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply baseMap_eq_zero K
  simp only [map_sub, hpq, sub_self]

end StableCoordinate.BundleCharts

end

end OAI
