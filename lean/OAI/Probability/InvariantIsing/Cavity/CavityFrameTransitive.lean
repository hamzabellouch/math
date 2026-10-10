import OAI.Probability.InvariantIsing.Cavity.CavityFrameAlgebra

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
