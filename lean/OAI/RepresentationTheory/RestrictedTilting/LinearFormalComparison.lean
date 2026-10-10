import OAI.RepresentationTheory.RestrictedTilting.MatrixFormalComparison
import OAI.RepresentationTheory.RestrictedTilting.CoordinateTensor

namespace OAI

namespace FiberFunctorProof
open Matrix
open scoped TensorProduct BigOperators
universe u v
variable {k : Type u} [Field k] [Infinite k]
variable {K : Type v} [Field K] [Algebra k K]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {T : Type u} [AddCommGroup T] [Module k T] [Module.Finite k T]

omit [Infinite k] in
lemma scalarCoordinates_one (v : ι → k) :
    (TensorProduct.piScalarRight k K K ι) (1 ⊗ₜ[k] v) = fun i => algebraMap k K (v i) := by
  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, mul_one]

omit [Infinite k] in
lemma scalarCoordinates_symm_base (v : ι → k) :
    (TensorProduct.piScalarRight k K K ι).symm (fun i => algebraMap k K (v i)) = 1 ⊗ₜ[k] v := by
  rw [← scalarCoordinates_one, LinearEquiv.symm_apply_apply]

omit [Infinite k] [DecidableEq ι] in
lemma eq_finrank_of_field_equiv (F : (K ⊗[k] T) ≃ₗ[K] (ι → K)) :
    Module.finrank k T = Module.finrank k (ι → k) := by
  rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_baseChange (R := K)]
  exact F.finrank_eq.trans (Module.finrank_fintype_fun_eq_card K)

 

theorem linear_formal_comparison
    (ρ : Representation k (SL2 k) T) (hρ : IsRational k ρ)
    (P : Matrix ι ι (Polynomial k)) (x : K) (hx : x ≠ 0)
    (F : (K ⊗[k] T) ≃ₗ[K] (ι → K))
    (hF : ∀ t : k, ∀ v : T,
      F (1 ⊗ₜ[k] ρ (unipotent k t) v) =
        polynomialMatrixEval P (algebraMap k K t / x^2) *ᵥ F (1 ⊗ₜ[k] v)) :
    ∃ E : T ≃ₗ[k] (ι → k), ∀ t : k, ∀ v : T,
      E (ρ (unipotent k t) v) = polynomialMatrixEval P t *ᵥ E v := by
  let e : T ≃ₗ[k] (ι → k) := LinearEquiv.ofFinrankEq T (ι → k) (eq_finrank_of_field_equiv F)
  let τ := coordinateRepresentation k ρ e
  have hτ : IsRational k τ := coordinateRepresentation_rational k ρ e hρ
  let Q := TensorProduct.piScalarRight k K K ι
  let C₀ : (ι → K) ≃ₗ[K] (ι → K) := Q.symm ≪≫ₗ e.symm.baseChange k K _ _ ≪≫ₗ F
  let C := LinearMap.toMatrix' C₀.toLinearMap
  have hC : C.det ≠ 0 := (C₀.isUnit_det (Pi.basisFun K ι) (Pi.basisFun K ι)).ne_zero
  have hCv (v : ι → k) : C *ᵥ (fun i => algebraMap k K (v i)) = F (1 ⊗ₜ[k] e.symm v) := by
    rw [LinearMap.toMatrix'_mulVec]
    change F (e.symm.baseChange k K _ _ (Q.symm (fun i => algebraMap k K (v i)))) = _
    rw [scalarCoordinates_symm_base, LinearEquiv.baseChange_tmul]
  have hCeq (t : k) : C * (LinearMap.toMatrix' (τ (unipotent k t))).map (algebraMap k K) =
      polynomialMatrixEval P (algebraMap k K t / x^2) * C := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hsingle : (Pi.single j 1 : ι → K) = fun i => algebraMap k K ((Pi.single j 1 : ι → k) i) := by
      funext i
      simp [Pi.single_apply]
    have hmap (B : Matrix ι ι k) (v : ι → k) :
        B.map (algebraMap k K) *ᵥ (fun i => algebraMap k K (v i)) =
          fun i => algebraMap k K ((B *ᵥ v) i) := by
      funext i
      exact (RingHom.map_mulVec (algebraMap k K) B v i).symm
    rw [hsingle, hmap, hCv, hCv, LinearMap.toMatrix'_mulVec]
    have heq : e.symm (τ (unipotent k t) (Pi.single j 1)) =
        ρ (unipotent k t) (e.symm (Pi.single j 1)) := by
      apply e.injective
      rw [e.apply_symm_apply, coordinateRepresentation_equiv, e.apply_symm_apply]
    rw [heq]
    exact hF t _
  obtain ⟨D,hD,heD⟩ := matrix_formal_comparison τ hτ P x hx C hC hCeq
  let E₀ := Matrix.toLinearEquiv (Pi.basisFun k ι) D (isUnit_iff_ne_zero.mpr hD)
  have hE₀ (v : ι → k) : E₀ v = D *ᵥ v := by
    rw [Matrix.toLinearEquiv_apply]
    rfl
  refine ⟨e.trans E₀, fun t v => ?_⟩
  simp only [LinearEquiv.trans_apply, hE₀, coordinateRepresentation_equiv]
  rw [← LinearMap.toMatrix'_mulVec (τ (unipotent k t)), Matrix.mulVec_mulVec,
    ← heD, ← Matrix.mulVec_mulVec]
end FiberFunctorProof

end OAI
