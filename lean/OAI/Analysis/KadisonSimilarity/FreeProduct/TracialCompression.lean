import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralFourier
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns
import Mathlib.Algebra.Star.Subalgebra

namespace OAI

/-! Dense tracial vectors determine the word-level operator compression.
In particular the matrix-entry identity is proved from the trace and the
two-sided expectation identity, rather than supplied as an operator hypothesis. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [CompleteSpace K] in
/-- Matrix coefficients on any dense family determine a bounded operator. -/
theorem operator_eq_of_dense_coefficients {ι : Type*} (v : ι → K)
    (hv : DenseRange v) (A B : K →L[ℂ] K)
    (h : ∀ i j, inner ℂ (v i) (A (v j)) = inner ℂ (v i) (B (v j))) : A = B := by
  have hvec (j : ι) : A (v j) = B (v j) := by
    apply ext_inner_left ℂ
    have heq := hv.equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      (funext (fun i => h i j))
    exact congrFun heq
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer A.continuous B.continuous (funext hvec))

variable {R : Type*} [Ring R] [StarRing R]

/-- Star reverses the exponent of a unitary, in the units convention used in
the dihedral word calculation. -/
theorem star_unitary_zpow (w : Rˣ) (hw : star w = w⁻¹) (j : ℤ) :
    star ((↑(w ^ j) : R)) = (↑(w ^ (-j)) : R) := by
  rw [← Units.coe_star, star_zpow, hw, inv_zpow, zpow_neg]

/-- Removing the supporting corner in a tracial word leaves precisely the
two Fourier powers around the test operator. -/
theorem tracial_corner_word (w : Rˣ) (hw : star w = w⁻¹)
    (e h a b : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (j k : ℤ) :
    star (e * (↑(w ^ (-j)) : R) * a) *
        (h * (e * (↑(w ^ (-k)) : R) * b)) =
      star a * ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) * b := by
  rw [star_mul, star_mul, star_unitary_zpow w hw, neg_neg, he]
  calc
    _ = star a * (↑(w ^ j) : R) * (e * h * e) * (↑(w ^ (-k)) : R) * b := by
      simp only [mul_assoc]
    _ = _ := by rw [heh, hhe]; simp only [mul_assoc]

variable [Algebra ℂ R] [StarModule ℂ R]

/-- A trace-preserving bimodule projection preserves all matrix coefficients
against its range algebra. -/
theorem tracial_expectation_test (A : StarSubalgebra ℂ R)
    (τ : R →ₗ[ℂ] ℂ) (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R)) (a b : A) (x : R) :
    τ (star (a : R) * x * (b : R)) = τ (star (a : R) * E x * (b : R)) := by
  have h := htrace (star (a : R) * x * (b : R))
  have he : E (star (a : R) * x * (b : R)) = star (a : R) * E x * (b : R) :=
    hbimod (star a) b x
  rw [he] at h
  exact h.symm

/-- Word-level compression computed from dense tracial vectors. `ρ` is the
compression of the left action to the base Hilbert space; it need only be
linear on the full algebra. -/
theorem tracial_word_compression_entry
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R))
    (w : Rˣ) (hw : star w = w⁻¹) (e h : R)
    (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (c q : ℂ) (hc : star c * c = q) (j k : ℤ)
    (Uj Uk : K →L[ℂ] H)
    (hUj : ∀ a : A, Uj (v a) = c • V (e * (↑(w ^ (-j)) : R) * (a : R)))
    (hUk : ∀ a : A, Uk (v a) = c • V (e * (↑(w ^ (-k)) : R) * (a : R))) :
    Uj.adjoint.comp ((L h).comp Uk) =
      q • ρ (E ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R))) := by
  apply operator_eq_of_dense_coefficients v hv
  intro a b
  change inner ℂ (v a) (Uj.adjoint (L h (Uk (v b)))) =
    inner ℂ (v a) (q • ρ (E _) (v b))
  change (starRingEnd ℂ) c * c = q at hc
  rw [ContinuousLinearMap.adjoint_inner_right, hUj, hUk, map_smul,
    inner_smul_left, inner_smul_right, hleft, hinner,
    tracial_corner_word w hw e h (a : R) (b : R) he heh hhe j k,
    tracial_expectation_test A τ E htrace hbimod a b,
    inner_smul_right, hρ, ← mul_assoc, hc]

omit [StarRing R] [StarModule ℂ R] in
/-- Once the algebraic entry calculation is known, linearity and the exact
corner normalization give the whole finite Toeplitz-plus-Hankel matrix. -/
theorem finite_dihedral_compression
    {N : ℕ} (U : Fin N → K →L[ℂ] H) (T : H →L[ℂ] H)
    (ρ : R →ₗ[ℂ] (K →L[ℂ] K)) (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (s : R) (γ : ℤ → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hentry : ∀ i j,
      (U i).adjoint.comp (T.comp (U j)) =
        t⁻¹ • ρ (((2 * t) ^ 2 / 2) •
          (γ ((i : ℕ) - (j : ℤ)) • (1 : R) +
            γ ((i : ℕ) + (j : ℤ) + 1) • s))) :
    (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      (2 * t) • matrixOperator (fun i j =>
        γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
          γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
  have he : (fun i j => (U i).adjoint.comp (T.comp (U j))) =
      fun (i j : Fin N) => (2 * t) • (γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
        γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
    funext i j
    rw [hentry, map_smul, map_add, map_smul, map_smul, hρone,
      smul_smul, normalized_corner_scalar t ht]
  rw [sumColumns_compression, he]
  ext x i
  simp [matrixOperator, Finset.smul_sum]

end KadisonSimilarity

end

end OAI
