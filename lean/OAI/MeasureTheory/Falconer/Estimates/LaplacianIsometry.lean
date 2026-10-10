import OAI.MeasureTheory.Falconer.Fourier.PublishedQuadraticStationary

namespace OAI

/-!
# Rotation invariance and locality of the actual quadratic jets

These are identities for the Euclidean derivatives in the published input.
They allow the choice of tangent orthonormal coordinates and fixed cutoffs
to be removed from the resulting stationary coefficients.
-/

namespace Falconer
open InnerProductSpace
open scoped Topology

theorem euclidean_laplacian_isometry {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (f : Space n → ℂ) :
    Laplacian.laplacian (f ∘ e) = (Laplacian.laplacian f) ∘ e := by
  let B := EuclideanSpace.basisFun (Fin n) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) B,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (B.map e)]
  funext x
  have hd := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (x := x) (Set.mem_univ (e x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at hd
  apply Finset.sum_congr rfl
  intro i _
  rw [hd]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem euclidean_iterated_laplacian_isometry {n : ℕ}
    (e : Space n ≃ₗᵢ[ℝ] Space n) (f : Space n → ℂ) (j : ℕ) :
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] (f ∘ e)) =
      (((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) ∘ e) := by
  induction j with
  | zero => rfl
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hj,
        euclidean_laplacian_isometry]

theorem quadraticJetCoefficient_isometry {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (f : Space n → ℂ) (j : ℕ) :
    quadraticJetCoefficient j (f ∘ e) = quadraticJetCoefficient j f := by
  simp only [quadraticJetCoefficient, euclidean_iterated_laplacian_isometry,
    Function.comp_apply, map_zero]

theorem euclidean_iterated_laplacian_congr {n : ℕ} {f g : Space n → ℂ}
    {x : Space n} (h : f =ᶠ[𝓝 x] g) (j : ℕ) :
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) =ᶠ[𝓝 x]
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] g) := by
  induction j with
  | zero => exact h
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact laplacian_congr_nhds hj

theorem quadraticJetCoefficient_congr {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᶠ[𝓝 (0 : Space n)] g) (j : ℕ) :
    quadraticJetCoefficient j f = quadraticJetCoefficient j g := by
  unfold quadraticJetCoefficient
  rw [(euclidean_iterated_laplacian_congr h j).self_of_nhds]

end Falconer

end OAI
