import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap

namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

noncomputable def frameLinearMap (v : Fin h → Space d) : Space h →ₗ[ℝ] Space d :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr ℝ v

@[simp] theorem frameLinearMap_basis (v : Fin h → Space d) (i : Fin h) :
    frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr_basis ℝ v i

theorem frameLinearMap_orthonormal {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameLinearMap v ∘ (EuclideanSpace.basisFun (Fin h) ℝ).toBasis) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  change inner ℝ (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i))
    (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ j)) = _
  simpa only [frameLinearMap_basis] using hv i j

theorem orthonormal_frame_embedding {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    ∃ e : Space h →ₗᵢ[ℝ] Space d,
      ∀ i, e (EuclideanSpace.basisFun (Fin h) ℝ i) = v i := by
  let e : Space h →ₗᵢ[ℝ] Space d := (frameLinearMap v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal (frameLinearMap_orthonormal hv)
  refine ⟨e,?_⟩
  intro i
  change frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i
  exact frameLinearMap_basis v i

end Falconer

end OAI
