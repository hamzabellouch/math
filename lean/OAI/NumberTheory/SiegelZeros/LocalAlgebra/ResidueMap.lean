import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.SiegelZeros.Differentials.ConormalNonvanishing
import OAI.NumberTheory.SiegelZeros.Intersection.TorusProjectiveClosure

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W14

section LogDifferential
variable {k K : Type*} [CommRing k] [Field K] [Algebra k K]

noncomputable def logDifferential (x : K) : Ω[K⁄k] :=
  x⁻¹ • KaehlerDifferential.D k K x

@[simp] theorem logDifferential_one : logDifferential (k := k) (1 : K) = 0 := by
  simp [logDifferential]

theorem logDifferential_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    logDifferential (k := k) (x * y) =
      logDifferential (k := k) x + logDifferential (k := k) y := by
  simp only [logDifferential, Derivation.leibniz, smul_add, smul_smul]
  have h₁ : (x * y)⁻¹ * x = y⁻¹ := by field_simp
  have h₂ : (x * y)⁻¹ * y = x⁻¹ := by field_simp
  rw [h₁, h₂, add_comm]

theorem logDifferential_pow {x : K} (hx : x ≠ 0) (n : ℕ) :
    logDifferential (k := k) (x ^ n) = n • logDifferential (k := k) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, logDifferential_mul (pow_ne_zero n hx) hx, ih, succ_nsmul]

theorem logDifferential_inv {x : K} (hx : x ≠ 0) :
    logDifferential (k := k) x⁻¹ = -logDifferential (k := k) x := by
  have h := logDifferential_mul (k := k) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, logDifferential_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem logDifferential_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    logDifferential (k := k) (x / y) =
      logDifferential (k := k) x - logDifferential (k := k) y := by
  rw [div_eq_mul_inv, logDifferential_mul hx (inv_ne_zero hy),
    logDifferential_inv hy, sub_eq_add_neg]

end LogDifferential

section DVR
variable {k R K : Type*} [CommRing k] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K]

omit [Algebra k R] [IsScalarTower k R K] in
theorem dvr_logDifferential_decomposition {x π : R} (hx : x ≠ 0)
    (hπ : Irreducible π) :
    ∃ (n : ℕ) (u : Rˣ),
      x = (u : R) * π ^ n ∧
      IsDiscreteValuationRing.addVal R x = n ∧
      logDifferential (k := k) (algebraMap R K x) =
        logDifferential (k := k) (algebraMap R K (u : R)) +
          n • logDifferential (k := k) (algebraMap R K π) := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  refine ⟨n, u, hu, IsDiscreteValuationRing.addVal_def x u hπ n hu, ?_⟩
  have hinj := IsFractionRing.injective R K
  have hu0 : algebraMap R K (u : R) ≠ 0 :=
    (u.isUnit.map (algebraMap R K)).ne_zero
  have hπ0 : algebraMap R K π ≠ 0 := by
    exact fun h => hπ.ne_zero (hinj (by simpa using h))
  rw [hu, map_mul, map_pow, logDifferential_mul hu0 (pow_ne_zero n hπ0),
    logDifferential_pow hπ0]

omit [Algebra k R] [IsScalarTower k R K] in
theorem fraction_logDifferential_decomposition {f : K} (hf : f ≠ 0)
    {π : R} (hπ : Irreducible π) :
    ∃ (x y : R) (n m : ℕ) (u v : Rˣ),
      f = algebraMap R K x / algebraMap R K y ∧
      IsDiscreteValuationRing.addVal R x = n ∧
      IsDiscreteValuationRing.addVal R y = m ∧
      logDifferential (k := k) f =
        (logDifferential (k := k) (algebraMap R K (u : R)) -
          logDifferential (k := k) (algebraMap R K (v : R))) +
        ((n : ℤ) - (m : ℤ)) • logDifferential (k := k) (algebraMap R K π) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
  have hx0 : algebraMap R K x ≠ 0 := by
    intro hx
    apply hf
    rw [← hxy, hx, zero_div]
  have hy0 : algebraMap R K y ≠ 0 := by
    intro hy'
    apply hf
    rw [← hxy, hy', div_zero]
  have hx : x ≠ 0 := fun h => hx0 (by simp [h])
  have hy' : y ≠ 0 := fun h => hy0 (by simp [h])
  obtain ⟨n, u, _, hn, hdu⟩ := dvr_logDifferential_decomposition (k := k) (K := K) hx hπ
  obtain ⟨m, v, _, hm, hdv⟩ := dvr_logDifferential_decomposition (k := k) (K := K) hy' hπ
  refine ⟨x, y, n, m, u, v, hxy.symm, hn, hm, ?_⟩
  rw [← hxy, logDifferential_div hx0 hy0, hdu, hdv]
  simp only [sub_zsmul, natCast_zsmul]
  abel

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem local_unit_logDifferential_is_regular (u : Rˣ) :
    logDifferential (k := k) (algebraMap R K (u : R)) =
      KaehlerDifferential.map k k R K
        ((↑u⁻¹ : R) • KaehlerDifferential.D k R (u : R)) := by
  have huinv : algebraMap R K (↑u⁻¹ : R) = (algebraMap R K (u : R))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    simp
  rw [map_smul, KaehlerDifferential.map_D,
    ← algebraMap_smul K (↑u⁻¹ : R), huinv]
  rfl

noncomputable def regularDifferentials : Submodule R Ω[K⁄k] :=
  LinearMap.range (KaehlerDifferential.map k k R K)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem local_unit_logDifferential_class_zero (u : Rˣ) :
    (regularDifferentials (k := k) (R := R) (K := K)).mkQ
      (logDifferential (k := k) (algebraMap R K (u : R))) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨(↑u⁻¹ : R) • KaehlerDifferential.D k R (u : R),
    (local_unit_logDifferential_is_regular (k := k) u).symm⟩

theorem uniformizer_smul_logDifferential_class_zero {π : R} (hπ : Irreducible π) :
    π • (regularDifferentials (k := k) (R := R) (K := K)).mkQ
      (logDifferential (k := k) (algebraMap R K π)) = 0 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact (IsFractionRing.injective R K) (by simpa using h)
  rw [← map_smul, ← algebraMap_smul K π, logDifferential, smul_smul,
    mul_inv_cancel₀ hπ0, one_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨KaehlerDifferential.D k R π, KaehlerDifferential.map_D k k R K π⟩

theorem fraction_logDifferential_class {f : K} (hf : f ≠ 0)
    {π : R} (hπ : Irreducible π) :
    ∃ z : ℤ,
      (regularDifferentials (k := k) (R := R) (K := K)).mkQ
        (logDifferential (k := k) f) =
      z • (regularDifferentials (k := k) (R := R) (K := K)).mkQ
        (logDifferential (k := k) (algebraMap R K π)) := by
  obtain ⟨x, y, n, m, u, v, _, _, _, h⟩ :=
    fraction_logDifferential_decomposition (k := k) (R := R) hf hπ
  refine ⟨(n : ℤ) - (m : ℤ), ?_⟩
  rw [h, map_add, map_sub, map_zsmul,
    local_unit_logDifferential_class_zero, local_unit_logDifferential_class_zero]
  simp

end DVR

end SiegelZerosAwei.Workers.W14

end

section

noncomputable section
namespace SiegelZerosAwei.Workers.W14

open scoped TensorProduct BigOperators

variable {k R K : Type*} [CommRing k] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra k R] [Algebra R K]
    [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K]

local notation "κ" => IsLocalRing.ResidueField R

def logarithmicPresentation (π : R) : (Ω[R⁄k] × R) →ₗ[R] Ω[K⁄k] :=
  (KaehlerDifferential.map k k R K).comp (LinearMap.fst R Ω[R⁄k] R) +
    (LinearMap.toSpanSingleton R Ω[K⁄k]
      (logDifferential (k := k) (algebraMap R K π))).comp
        (LinearMap.snd R Ω[R⁄k] R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] theorem logarithmicPresentation_apply (π : R) (ω : Ω[R⁄k]) (r : R) :
    logarithmicPresentation (k := k) (K := K) π (ω, r) =
      KaehlerDifferential.map k k R K ω +
        r • logDifferential (k := k) (algebraMap R K π) := rfl

def logarithmicLattice (π : R) : Submodule R Ω[K⁄k] :=
  LinearMap.range (logarithmicPresentation (k := k) (K := K) π)

def logarithmicCoefficient : (Ω[R⁄k] × R) →ₗ[R] κ :=
  (Algebra.linearMap R κ).comp (LinearMap.snd R Ω[R⁄k] R)

@[simp] theorem logarithmicCoefficient_apply (ω : Ω[R⁄k]) (r : R) :
    logarithmicCoefficient (k := k) (ω, r) = algebraMap R κ r := rfl

section Smooth
variable [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]

theorem exists_normalized_regular_functional {π : R} (hπ : Irreducible π) :
    ∃ L : Ω[R⁄k] →ₗ[R] κ, L (KaehlerDifferential.D k R π) = 1 := by
  have hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hmem : π ∈ RingHom.ker (algebraMap R κ) := by
    rw [hker, hπ.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have hnot : π ∉ (RingHom.ker (algebraMap R κ)) ^ 2 := by
    rw [hker]
    exact uniformizer_not_mem_maximalIdeal_sq hπ
  have hn : (1 : κ) ⊗ₜ[R] (KaehlerDifferential.D k R π) ≠ 0 :=
    smooth_conormal_tensor_ne_zero
      (by simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_surjective (R := R))) ⟨π, hmem⟩ hnot
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one κ hn
  refine ⟨(l.restrictScalars R).comp (TensorProduct.mk R κ Ω[R⁄k] 1), ?_⟩
  exact hl

omit [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k κ] in
theorem uniformizer_smul_logDifferential {π : R} (hπ : Irreducible π) :
    π • logDifferential (k := k) (algebraMap R K π) =
      KaehlerDifferential.D k K (algebraMap R K π) := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective R K) (by simpa using h))
  rw [← algebraMap_smul K π, logDifferential, smul_smul,
    mul_inv_cancel₀ hπ0, one_smul]

theorem logarithmicPresentation_ker_le_coefficient_ker {π : R} (hπ : Irreducible π) :
    LinearMap.ker (logarithmicPresentation (k := k) (K := K) π) ≤
      LinearMap.ker (logarithmicCoefficient (k := k) (R := R)) := by
  rintro ⟨ω, r⟩ h
  change KaehlerDifferential.map k k R K ω +
      r • logDifferential (k := k) (algebraMap R K π) = 0 at h
  change algebraMap R κ r = 0
  have hinj := SiegelZeros.W58.smooth_kaehler_localization_injective
    (k := k) (R := R) (S := K) (nonZeroDivisors R) le_rfl
  have hregular : π • ω + r • KaehlerDifferential.D k R π = 0 := by
    apply hinj
    rw [map_zero, map_add, map_smul, map_smul, KaehlerDifferential.map_D]
    rw [← uniformizer_smul_logDifferential (K := K) hπ, smul_comm r π,
      ← smul_add, h, smul_zero]
  obtain ⟨L, hL⟩ := exists_normalized_regular_functional (k := k) hπ
  have hπres : algebraMap R κ π = 0 := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      hπ.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have hLrel := congrArg L hregular
  simpa only [map_add, map_smul, Algebra.smul_def, hπres, zero_mul,
    zero_add, hL, mul_one, map_zero] using hLrel

def logarithmicResidue {π : R} (hπ : Irreducible π) :
    logarithmicLattice (k := k) (K := K) π →ₗ[R] κ :=
  ((LinearMap.ker (logarithmicPresentation (k := k) (K := K) π)).liftQ
    (logarithmicCoefficient (k := k))
    (logarithmicPresentation_ker_le_coefficient_ker (K := K) hπ)).comp
      (logarithmicPresentation (k := k) (K := K) π).quotKerEquivRange.symm.toLinearMap

theorem logarithmicResidue_presentation {π : R} (hπ : Irreducible π)
    (ω : Ω[R⁄k]) (r : R) :
    logarithmicResidue (K := K) hπ
      ⟨logarithmicPresentation (k := k) (K := K) π (ω, r),
        LinearMap.mem_range_self _ _⟩ = algebraMap R κ r := by
  exact congrArg
    ((LinearMap.ker (logarithmicPresentation (k := k) (K := K) π)).liftQ
      (logarithmicCoefficient (k := k))
      (logarithmicPresentation_ker_le_coefficient_ker (K := K) hπ))
    (LinearMap.quotKerEquivRange_symm_apply_image
      (logarithmicPresentation (k := k) (K := K) π) (ω, r)
      (LinearMap.mem_range_self _ _))

omit [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k κ] in
theorem fraction_logarithmicPresentation {f : K} (hf : f ≠ 0)
    {π : R} (hπ : Irreducible π) :
    ∃ (x y : R) (n m : ℕ) (ω : Ω[R⁄k]),
      f = algebraMap R K x / algebraMap R K y ∧
      IsDiscreteValuationRing.addVal R x = n ∧
      IsDiscreteValuationRing.addVal R y = m ∧
      logarithmicPresentation (k := k) (K := K) π
        (ω, (((n : ℤ) - (m : ℤ) : ℤ) : R)) = logDifferential (k := k) f := by
  obtain ⟨x, y, n, m, u, v, hxy, hn, hm, hd⟩ :=
    fraction_logDifferential_decomposition (k := k) (R := R) hf hπ
  let ωu : Ω[R⁄k] := (↑u⁻¹ : R) • KaehlerDifferential.D k R (u : R)
  let ωv : Ω[R⁄k] := (↑v⁻¹ : R) • KaehlerDifferential.D k R (v : R)
  refine ⟨x, y, n, m, ωu - ωv, hxy, hn, hm, ?_⟩
  rw [logarithmicPresentation_apply, map_sub]
  rw [show KaehlerDifferential.map k k R K ωu =
    logDifferential (k := k) (algebraMap R K (u : R)) from
      (local_unit_logDifferential_is_regular (k := k) u).symm]
  rw [show KaehlerDifferential.map k k R K ωv =
    logDifferential (k := k) (algebraMap R K (v : R)) from
      (local_unit_logDifferential_is_regular (k := k) v).symm]
  rw [Int.cast_smul_eq_zsmul]
  exact hd.symm

theorem logarithmicResidue_dlog {f : K} (hf : f ≠ 0)
    {π : R} (hπ : Irreducible π) :
    ∃ (x y : R) (n m : ℕ)
      (hmem : logDifferential (k := k) f ∈ logarithmicLattice (k := k) (K := K) π),
      f = algebraMap R K x / algebraMap R K y ∧
      IsDiscreteValuationRing.addVal R x = n ∧
      IsDiscreteValuationRing.addVal R y = m ∧
      logarithmicResidue (K := K) hπ ⟨logDifferential (k := k) f, hmem⟩ =
        (((n : ℤ) - (m : ℤ) : ℤ) : κ) := by
  obtain ⟨x, y, n, m, ω, hxy, hn, hm, hω⟩ :=
    fraction_logarithmicPresentation (k := k) (R := R) hf hπ
  have hmem : logDifferential (k := k) f ∈ logarithmicLattice (k := k) (K := K) π :=
    ⟨(ω, (((n : ℤ) - (m : ℤ) : ℤ) : R)), hω⟩
  refine ⟨x, y, n, m, hmem, hxy, hn, hm, ?_⟩
  have hres := logarithmicResidue_presentation (K := K) hπ ω
    ((((n : ℤ) - (m : ℤ) : ℤ)) : R)
  have heq : (⟨logarithmicPresentation (k := k) (K := K) π
      (ω, ((((n : ℤ) - (m : ℤ) : ℤ)) : R)), LinearMap.mem_range_self _ _⟩ :
      logarithmicLattice (k := k) (K := K) π) =
      ⟨logDifferential (k := k) f, hmem⟩ := Subtype.ext hω
  rw [heq] at hres
  simpa only [map_intCast] using hres

theorem logarithmicResidue_sum_eq_zero {ι : Type*} [Fintype ι]
    {π : R} (hπ : Irreducible π) (c : ι → R)
    (ω : ι → logarithmicLattice (k := k) (K := K) π)
    (h : ∑ i, c i • (ω i : Ω[K⁄k]) = 0) :
    ∑ i, algebraMap R κ (c i) * logarithmicResidue (K := K) hπ (ω i) = 0 := by
  have hz : ∑ i, c i • ω i = 0 := by
    apply Subtype.ext
    simpa using h
  have hr := congrArg (logarithmicResidue (K := K) hπ) hz
  simpa only [map_sum, map_smul, Algebra.smul_def, map_zero] using hr

end Smooth
end SiegelZerosAwei.Workers.W14

end

end

end SiegelZeros

end OAI
