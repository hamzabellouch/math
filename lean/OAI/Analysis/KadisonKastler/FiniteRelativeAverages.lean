import OAI.Analysis.KadisonKastler.RelativeTraceAveraging
import OAI.Analysis.KadisonKastler.EqualWeightAverages
import OAI.Analysis.KadisonKastler.FiniteAveraging

namespace OAI

/-! # Finite unitary averages approximating the scalar trace -/

namespace KadisonKastler

open Set
open scoped BigOperators

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}
  {τ : FaithfulTracialState (Algebra M)}

/-- Scalar relative averaging is realized to any positive accuracy by a
nonempty finite equal-weight family of actual unitaries. -/
theorem exists_finite_relative_scalar_average
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ ((n : ℂ)⁻¹ • ∑ i, φ (u i) * a * star (φ (u i)) -
        τ.toLinearMap a • (1 : Algebra M)) < ε := by
  classical
  have hc := trace_scalar_mem_relativeOrbit_hull J hJ hτ φ hirr a
  rw [diagonalTraceHull_eq] at hc
  obtain ⟨n, hn, f, hf, hclose⟩ := exists_equalWeightAverage_of_mem_closedConvexHull hc hε
  have hex (i : Fin n) : ∃ u : unitary R, J (φ u * a * star (φ u)) = f i := by
    obtain ⟨x, ⟨u, rfl⟩, hx⟩ := hf i
    exact ⟨u, hx⟩
  choose u hu using hex
  refine ⟨n, hn, u, ?_⟩
  rw [← hJ, map_sub]
  have he : J ((n : ℂ)⁻¹ • ∑ i, φ (u i) * a * star (φ (u i))) =
      (n : ℝ)⁻¹ • ∑ i, f i := by
    rw [map_smul, map_sum]
    simp only [hu, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.coe_smul]
  rw [he]
  exact hclose

end

end KadisonKastler

end OAI
