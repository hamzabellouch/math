import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.Degrees

namespace OAI

namespace ArExplicit

abbrev ParameterRing := MvPolynomial (Fin 3) (ZMod 2)

abbrev BaseField := FractionRing ParameterRing

noncomputable def parameter (i : Fin 3) : BaseField :=
  algebraMap ParameterRing BaseField (MvPolynomial.X i)

noncomputable abbrev q : BaseField := parameter 0
noncomputable abbrev H₁ : BaseField := parameter 1
noncomputable abbrev H₂ : BaseField := parameter 2

theorem parameters_algebraicallyIndependent :
    AlgebraicIndependent (ZMod 2) parameter := by
  exact (MvPolynomial.algebraicIndependent_X (Fin 3) (ZMod 2)).map'
    (f := IsScalarTower.toAlgHom (ZMod 2) ParameterRing BaseField)
    (IsFractionRing.injective ParameterRing BaseField)

theorem parameter_ne_zero (i : Fin 3) : parameter i ≠ 0 := by
  exact parameters_algebraicallyIndependent.ne_zero i

theorem parameter_pow_ne_one (i : Fin 3) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ 1 := by
  intro h
  have he : (MvPolynomial.X i : ParameterRing) ^ n = 1 := by
    apply IsFractionRing.injective ParameterRing BaseField
    simpa only [map_pow, map_one, parameter] using h
  have hd := congrArg MvPolynomial.totalDegree he
  simp only [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_one] at hd
  omega

theorem parameter_pow_ne (i j : Fin 3) (hij : i ≠ j) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ parameter j ^ n := by
  intro h
  have he : (MvPolynomial.X i : ParameterRing) ^ n = MvPolynomial.X j ^ n := by
    apply IsFractionRing.injective ParameterRing BaseField
    simpa only [map_pow, parameter] using h
  have hd := congrArg (MvPolynomial.degreeOf i) he
  simp only [MvPolynomial.degreeOf_X_self_pow, MvPolynomial.degreeOf_X_pow_of_ne n hij] at hd
  omega

theorem q_pow_add_one_ne_zero (n : ℕ) (hn : 0 < n) : q ^ n + 1 ≠ 0 := by
  intro h
  apply parameter_pow_ne_one 0 n hn
  calc
    q ^ n = q ^ n + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [← add_assoc, h, zero_add]

theorem twist_eigenvalues_ne (n : ℕ) (hn : 0 < n) :
    (H₁ ^ n)⁻¹ ≠ (H₂ ^ n)⁻¹ := by
  intro h
  have := congrArg (fun x : BaseField => x⁻¹) h
  simp only [inv_inv] at this
  exact parameter_pow_ne 1 2 (by decide) n hn this

theorem twist_determinant_ne_zero (n : ℕ) (hn : 0 < n) :
    (H₁ ^ n)⁻¹ + (H₂ ^ n)⁻¹ ≠ 0 := by
  intro h
  apply twist_eigenvalues_ne n hn
  calc
    (H₁ ^ n)⁻¹ = (H₁ ^ n)⁻¹ + ((H₂ ^ n)⁻¹ + (H₂ ^ n)⁻¹) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (H₂ ^ n)⁻¹ := by rw [← add_assoc, h, zero_add]

theorem twist_determinant_ne_zero_after_extension
    (K : Type*) [Field K] [Algebra BaseField K] (n : ℕ) (hn : 0 < n) :
    algebraMap BaseField K ((H₁ ^ n)⁻¹ + (H₂ ^ n)⁻¹) ≠ 0 := by
  exact (map_ne_zero (algebraMap BaseField K)).mpr (twist_determinant_ne_zero n hn)

end ArExplicit

end OAI
