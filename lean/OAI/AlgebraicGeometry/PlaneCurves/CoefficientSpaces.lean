import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.Ring
import OAI.AlgebraicGeometry.PlaneCurves.Automorphic

namespace OAI

/-!
# Coefficient spaces of restricted normal polynomials
-/

section

/-!
# Actual automorphic coefficient spaces in §02
-/
namespace Nagata.CoefficientSpaces

/-- Multiplication by a fixed function power is a linear map on actual functions. -/
noncomputable def multiplyPower (P : ℂ → ℂ) (e : ℕ) :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := P z ^ e * f z
  map_add' f g := by funext z; simp [mul_add]
  map_smul' a f := by funext z; simp; ring

@[simp] theorem multiplyPower_apply (P f : ℂ → ℂ) (e : ℕ) (z : ℂ) :
    multiplyPower P e f z = P z ^ e * f z := rfl

/-- Multiplication by a genuine holomorphic automorphic section has exactly
the tensor-product transition multiplier and degree. -/
theorem multiplyPower_mem_sections {τ γ δ : ℂ} {n s : ℤ} {P f : ℂ → ℂ}
    (hP : P ∈ Nagata.W08.automorphicSections τ s δ)
    (hf : f ∈ Nagata.W08.automorphicSections τ n γ) (e : ℕ) :
    multiplyPower P e f ∈ Nagata.W08.automorphicSections τ
      (n + (e : ℤ) * s) (γ * δ ^ e) := by
  refine ⟨?_, ?_, ?_⟩
  · change P 0 ^ e * f 0 = 0
    rw [hf.1, mul_zero]
  · intro z hz
    exact ((hP.2.1 z hz).pow e).mul (hf.2.1 z hz)
  · intro z hz
    change P (τ * z) ^ e * f (τ * z) =
      (γ * δ ^ e) * z ^ (-(n + (e : ℤ) * s)) * (P z ^ e * f z)
    rw [hP.2.2 z hz, hf.2.2 z hz]
    have he : -(n + (e : ℤ) * s) = -n + (-s) * (e : ℤ) := by ring
    rw [he, zpow_add₀ hz, zpow_mul, zpow_natCast]
    simp only [mul_pow]
    ring

/-- The multiplier of A=L^3⊗O(-P), in fixed covering-space frames. -/
noncomputable def normalMinusMarkedMultiplier (γL γP : ℂ) : ℂ := γL ^ 3 / γP

/-- Coefficient block V_j of the actual polynomial space W_tau. Parameters d,m,j
are integers, so tensor exponents remain integer powers as in the source. -/
noncomputable def coefficientSpace (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    Nagata.W08.automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j))
  else
    (Nagata.W08.automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))).map
      (multiplyPower P (j - m).toNat)

/-- Membership in the second block means an actual section multiplied by P^(j-m). -/
theorem mem_coefficientSpace_second {τ γL γP : ℂ} {d m j : ℤ} {P g : ℂ → ℂ}
    (hj : m < j) :
    g ∈ coefficientSpace τ γL γP d m j P ↔
      ∃ f ∈ Nagata.W08.automorphicSections τ (3 * (d - 3 * j))
        (γL ^ (d - 3 * j)), multiplyPower P (j - m).toNat f = g := by
  rw [coefficientSpace, ite_eq_right (not_le.mpr hj)]
  exact Submodule.mem_map

/-- Every coefficient is genuinely holomorphic off zero. The positive-index
branch inherits this from its source section and the marked product. -/
theorem coefficientSpace_differentiableAt {τ γL γP : ℂ} {d m j : ℤ}
    {P f : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    (hf : f ∈ coefficientSpace τ γL γP d m j P) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ f z := by
  by_cases hj : j ≤ m
  · rw [coefficientSpace, ite_eq_left hj] at hf
    exact hf.2.1 z hz
  · obtain ⟨g, hg, rfl⟩ := (mem_coefficientSpace_second (lt_of_not_ge hj)).mp hf
    exact ((hP z hz).pow (j - m).toNat).mul (hg.2.1 z hz)

/-- The forced zero value at the omitted point introduces no extra coefficient. -/
theorem coefficientSpace_zero_value {τ γL γP : ℂ} {d m j : ℤ}
    {P f : ℂ → ℂ} (hf : f ∈ coefficientSpace τ γL γP d m j P) : f 0 = 0 := by
  by_cases hj : j ≤ m
  · rw [coefficientSpace, ite_eq_left hj] at hf
    exact hf.1
  · obtain ⟨g, hg, rfl⟩ := (mem_coefficientSpace_second (lt_of_not_ge hj)).mp hf
    change P 0 ^ (j - m).toNat * g 0 = 0
    rw [hg.1, mul_zero]

/-- Actual finite-degree polynomials in the fibre coordinate with coefficients
in the above spaces. The degree bound is imposed coefficientwise and therefore
includes the zero polynomial without a special degree convention. -/
noncomputable def polynomialSections (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (Polynomial (ℂ → ℂ)) where
  carrier := {F | (∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0) ∧
    ∀ j : ℕ, F.coeff j ∈ coefficientSpace τ γL γP d m (j : ℤ) P}
  zero_mem' := by
    constructor
    · intro j _; simp
    · intro j; simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj
      simp only [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj, add_zero]
    · intro j
      simpa only [Polynomial.coeff_add] using
        (coefficientSpace τ γL γP d m (j : ℤ) P).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj
      simp only [Polynomial.coeff_smul, hF.1 j hj, smul_zero]
    · intro j
      simpa only [Polynomial.coeff_smul] using
        (coefficientSpace τ γL γP d m (j : ℤ) P).smul_mem a (hF.2 j)

/-- The scalar expression of an actual polynomial section in the covering frame. -/
noncomputable def scalarExpression (F : Polynomial (ℂ → ℂ)) (z v : ℂ) : ℂ :=
  F.sum fun j f => f z * v ^ j

/-- Equality of every actual coefficient is equality of polynomial sections. -/
theorem polynomialSections_ext {τ γL γP : ℂ} {d m : ℤ} {P : ℂ → ℂ}
    (F G : polynomialSections τ γL γP d m P)
    (h : ∀ j, F.val.coeff j = G.val.coeff j) : F = G := by
  apply Subtype.ext
  exact Polynomial.ext h

end Nagata.CoefficientSpaces

end

end OAI
