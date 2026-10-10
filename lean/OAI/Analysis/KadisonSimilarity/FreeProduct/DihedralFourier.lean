import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

namespace OAI

/-! The exact dihedral word identity and the finite Fourier matrix entries. -/

noncomputable section
namespace KadisonSimilarity

section Group
variable {G : Type*} [Group G]

/-- The reflection relation fixes the sum-index in the Hankel term. -/
theorem dihedral_word_identity (w d : G) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    w ^ j * d * w ^ (-k) = w ^ (j + k + 1) * (w⁻¹ * d) := by
  have hmove : d * w ^ (-k) = w ^ k * d := by
    have h := (show SemiconjBy d w w⁻¹ from hd).zpow_right (-k)
    simpa only [inv_zpow, zpow_neg, inv_inv] using h.eq
  calc
    _ = w ^ j * (d * w ^ (-k)) := mul_assoc _ _ _
    _ = w ^ j * (w ^ k * d) := by rw [hmove]
    _ = w ^ (j + k) * d := by rw [← mul_assoc, ← zpow_add]
    _ = w ^ (j + k + 1) * (w⁻¹ * d) := by
      rw [← mul_assoc, ← zpow_neg_one, ← zpow_add]
      congr 2
      omega

end Group

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The corner of a symmetry, written algebraically. -/
def dihedralHalfProjection (d : Rˣ) : R := (1 / 2 : ℂ) • (1 + (d : R))

/-- Exact rotation-plus-reflection decomposition of the corner word. -/
theorem dihedral_corner_word (w d : Rˣ) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    (↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R) =
      (1 / 2 : ℂ) • ((↑(w ^ (j - k)) : R) +
        (↑(w ^ (j + k + 1)) : R) * (↑(w⁻¹ * d) : R)) := by
  have hrot : (↑(w ^ j) : R) * (↑(w ^ (-k)) : R) = (↑(w ^ (j - k)) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 1
  have href := congrArg (fun a : Rˣ => (a : R)) (dihedral_word_identity w d hd j k)
  simp only [Units.val_mul] at href
  simp only [dihedralHalfProjection, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_one, smul_add, Units.val_mul]
  rw [hrot, href]

/-- Once the two Fourier coefficient identities hold, the corner entry has
both its Toeplitz difference index and its Hankel sum-plus-one index. -/
theorem dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f : R) (E : R →ₗ[ℂ] R)
    (γ : ℤ → ℂ)
    (hrot : ∀ l : ℤ, E (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E (f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R))) =
      (1 / 2 : ℂ) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [dihedral_corner_word w d hd, mul_smul_comm, mul_add, ← mul_assoc,
    map_smul, map_add, hrot, href]

/-- The trace-orthogonal projection onto the span of a centered symmetry. -/
def symmetryExpectation (τ : R →ₗ[ℂ] ℂ) (s : R) : R →ₗ[ℂ] R where
  toFun x := τ x • 1 + τ (s * x) • s
  map_add' x y := by simp only [mul_add, map_add, add_smul]; abel
  map_smul' c x := by
    simp only [mul_smul_comm, map_smul, smul_add, smul_smul, RingHom.id_apply,
      smul_eq_mul]

@[simp] theorem symmetryExpectation_apply (τ : R →ₗ[ℂ] ℂ) (s x : R) :
    symmetryExpectation τ s x = τ x • 1 + τ (s * x) • s := rfl

/-- The two coefficients of `x` and `xs` exchange when `s²=1`. -/
theorem symmetryExpectation_mul_symmetry
    (τ : R →ₗ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (s x : R) (hs : s * s = 1) (hcoset : τ (s * x) = 0) :
    symmetryExpectation τ s x = τ x • 1 ∧
      symmetryExpectation τ s (x * s) = τ x • s := by
  constructor
  · simp only [symmetryExpectation_apply, hcoset, zero_smul, add_zero]
  · have hxs : τ (x * s) = 0 := (htr x s).trans hcoset
    have hconj : τ (s * (x * s)) = τ x := by
      rw [← mul_assoc, htr (s * x) s, ← mul_assoc, hs, one_mul]
    simp only [symmetryExpectation_apply, hxs, hconj, zero_smul, zero_add]

/-- Scalar group Fourier moments alone determine the finite compression
entry. The coset moment vanishes by dihedral group orthogonality. -/
theorem dihedral_fourier_entry_from_moments
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f : R)
    (τ : R →ₗ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hs : (↑(w⁻¹ * d) : R) * (↑(w⁻¹ * d) : R) = 1)
    (γ : ℤ → ℂ) (hcoef : ∀ l : ℤ, τ (f * (↑(w ^ l) : R)) = γ l)
    (hcoset : ∀ l : ℤ, τ ((↑(w⁻¹ * d) : R) * (f * (↑(w ^ l) : R))) = 0)
    (j k : ℤ) :
    symmetryExpectation τ (↑(w⁻¹ * d) : R)
        (f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R))) =
      (1 / 2 : ℂ) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  apply dihedral_fourier_entry w d hd f
  · intro l
    rw [(symmetryExpectation_mul_symmetry τ htr _ _ hs (hcoset l)).1, hcoef]
  · intro l
    rw [(symmetryExpectation_mul_symmetry τ htr _ _ hs (hcoset l)).2, hcoef]

/-- Bimodularity and the tower identity transfer the free-compression
expectation to a dihedral Fourier entry. -/
theorem compressed_dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f h : R)
    (EC E₀ : R →ₗ[ℂ] R) (γ : ℤ → ℂ) (u : ℂ)
    (hEC : EC h = u ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E₀ ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (u ^ 2 / 2) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [← htower j k, hbimod, hEC, mul_smul_comm, smul_mul_assoc, map_smul]
  have hproduct : (↑(w ^ j) : R) * (f * dihedralHalfProjection d) *
      (↑(w ^ (-k)) : R) =
      f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R)) := by
    rw [← mul_assoc (↑(w ^ j) : R) f, hcomm j]
    simp only [mul_assoc]
  rw [hproduct, dihedral_fourier_entry w d hd f E₀ γ hrot href, smul_smul]
  congr 1
  ring

/-- The normalized corner coefficient is exactly `u` when `u = 2t`. -/
theorem normalized_corner_scalar (t : ℂ) (ht : t ≠ 0) :
    t⁻¹ * ((2 * t) ^ 2 / 2) = 2 * t := by field_simp

end Algebra
end KadisonSimilarity

end

end OAI
