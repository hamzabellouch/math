import OAI.AlgebraicGeometry.CommutingDerivations.ParameterRetraction
import OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

namespace OAI

/-! The explicit intersection proof retains every dimension n >= 4 and
identifies its ordinary polynomial side with the standard subalgebra C[F_n]. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

def extendedAmbientParameter {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  extendedF hn + 1

def extendedParameterSlice {n : ℕ} (_hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i : Fin n => if i.val = 0 then Polynomial.X else 0)

theorem extendedParameterSlice_rename {n : ℕ} (hn : 4 ≤ n) (q : R) :
    extendedParameterSlice hn (MvPolynomial.rename (fourInclusion hn) q) = parameterSlice q := by
  unfold extendedParameterSlice parameterSlice
  rw [MvPolynomial.aeval_rename]
  have he : (fun i : Fin n => if i.val = 0 then (Polynomial.X : Polynomial ℂ) else 0) ∘
      fourInclusion hn = (fun i : Fin 4 => if i = 0 then Polynomial.X else 0) := by
    funext i
    change (if i.val = 0 then (Polynomial.X : Polynomial ℂ) else 0) =
      (if i = 0 then Polynomial.X else 0)
    by_cases hi : i = 0
    · subst i
      rfl
    · have hv : i.val ≠ 0 := fun hh => hi (Fin.ext hh)
      rw [ite_eq_right hv, ite_eq_right hi]
  rw [he]

@[simp] theorem extendedParameterSlice_parameter {n : ℕ} (hn : 4 ≤ n) :
    extendedParameterSlice hn (extendedAmbientParameter hn) = Polynomial.X := by
  have he : extendedAmbientParameter hn = MvPolynomial.rename (fourInclusion hn) ambientParameter := by
    simp [extendedAmbientParameter, extendedF, ambientParameter]
  rw [he, extendedParameterSlice_rename, parameterSlice_parameter]

theorem extendedParameterSlice_aeval {n : ℕ} (hn : 4 ≤ n) :
    (extendedParameterSlice hn).comp (Polynomial.aeval (extendedAmbientParameter hn)) =
      AlgHom.id ℂ (Polynomial ℂ) := by
  apply Polynomial.algHom_ext
  simp

@[simp] theorem extendedParameterSlice_aeval_apply {n : ℕ} (hn : 4 ≤ n) (q : Polynomial ℂ) :
    extendedParameterSlice hn (Polynomial.aeval (extendedAmbientParameter hn) q) = q :=
  AlgHom.congr_fun (extendedParameterSlice_aeval hn) q

theorem extendedParameter_aeval_injective {n : ℕ} (hn : 4 ≤ n) :
    Function.Injective (Polynomial.aeval (extendedAmbientParameter hn) :
      Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) :=
  (show Function.LeftInverse (extendedParameterSlice hn)
    (Polynomial.aeval (extendedAmbientParameter hn) :
      Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) from
      extendedParameterSlice_aeval_apply hn).injective

theorem extendedParameter_ne_zero {n : ℕ} (hn : 4 ≤ n) : extendedAmbientParameter hn ≠ 0 := by
  intro hh
  have he := congrArg (extendedParameterSlice hn) hh
  simp at he

theorem extendedParameter_power_saturated {n : ℕ} (hn : 4 ≤ n)
    (a : MvPolynomial (Fin n) ℂ) (q : Polynomial ℂ) (m : ℕ)
    (he : (extendedAmbientParameter hn)^m * a = Polynomial.aeval (extendedAmbientParameter hn) q) :
    a = Polynomial.aeval (extendedAmbientParameter hn) (extendedParameterSlice hn a) := by
  apply mul_left_cancel₀ (pow_ne_zero m (extendedParameter_ne_zero hn))
  have hh := congrArg (Polynomial.aeval (extendedAmbientParameter hn) :
      Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ)
    (congrArg (extendedParameterSlice hn) he)
  have hh' : (extendedAmbientParameter hn)^m *
      Polynomial.aeval (extendedAmbientParameter hn) (extendedParameterSlice hn a) =
      Polynomial.aeval (extendedAmbientParameter hn) q := by
    simpa only [map_mul, map_pow, extendedParameterSlice_parameter,
      extendedParameterSlice_aeval_apply, Polynomial.aeval_X] using hh
  exact he.trans hh'.symm

theorem extendedParameter_localization_injective {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] :
    Function.Injective (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
  apply IsLocalization.injective L (M := Submonoid.powers (extendedAmbientParameter hn))
  intro z hz
  obtain ⟨m, rfl⟩ := hz
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m (extendedParameter_ne_zero hn))

/-- Replacing f by f+1 does not change the literal polynomial-expression set. -/
theorem exists_aeval_add_one_iff {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (f a : A) :
    (∃ q : Polynomial K, a = Polynomial.aeval (f + 1) q) ↔
      ∃ q : Polynomial K, a = Polynomial.aeval f q := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (Polynomial.X + 1), ?_⟩
    simp [Polynomial.aeval_comp]
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (Polynomial.X - 1), ?_⟩
    simp [Polynomial.aeval_comp]

/-- Complete dimension-quantified intersection in the standard subalgebra
representation of C[F_n], with localization membership given by one Laurent
denominator and an ordinary polynomial numerator. -/
theorem extendedParameter_laurent_intersection {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] (a : MvPolynomial (Fin n) ℂ) :
    (∃ (m : ℕ) (q : Polynomial ℂ),
      (algebraMap (MvPolynomial (Fin n) ℂ) L (extendedAmbientParameter hn))^m *
          algebraMap (MvPolynomial (Fin n) ℂ) L a =
        algebraMap (MvPolynomial (Fin n) ℂ) L (Polynomial.aeval (extendedAmbientParameter hn) q)) ↔
    a ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  have hex :
      (∃ (m : ℕ) (q : Polynomial ℂ),
        (algebraMap (MvPolynomial (Fin n) ℂ) L (extendedAmbientParameter hn))^m *
            algebraMap (MvPolynomial (Fin n) ℂ) L a =
          algebraMap (MvPolynomial (Fin n) ℂ) L (Polynomial.aeval (extendedAmbientParameter hn) q)) ↔
      ∃ q : Polynomial ℂ, a = Polynomial.aeval (extendedAmbientParameter hn) q := by
    constructor
    · rintro ⟨m, q, hq⟩
      refine ⟨extendedParameterSlice hn a, extendedParameter_power_saturated hn a q m ?_⟩
      apply extendedParameter_localization_injective hn L
      simpa only [map_mul, map_pow] using hq
    · rintro ⟨q, rfl⟩
      exact ⟨0, q, by simp⟩
  rw [hex, extendedAmbientParameter, exists_aeval_add_one_iff,
    Algebra.adjoin_singleton_eq_range_aeval]
  change (∃ q : Polynomial ℂ, a = Polynomial.aeval (extendedF hn) q) ↔
    ∃ q : Polynomial ℂ, Polynomial.aeval (extendedF hn) q = a
  simp only [eq_comm]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
