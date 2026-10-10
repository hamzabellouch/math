import OAI.Geometry.NodalSets.Elliptic.BasisLaplacian

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma basisMetricMatrix_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix (b.reindex e) B = (basisMetricMatrix b B).submatrix e.symm e.symm := by
  ext i j
  simp [basisMetricMatrix,LinearMap.toMatrix₂_apply]

lemma basisMetricFlux_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (i : m) (y : E) :
    basisMetricFlux (b.reindex e) B f i y = basisMetricFlux b B f (e.symm i) y := by
  simp only [basisMetricFlux,basisMetricMatrix_reindex,det_submatrix_equiv_self,
    inv_submatrix_equiv,submatrix_apply,Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ (basisMetricMatrix b (B y))⁻¹ (e.symm i) j *
    fderiv ℝ f y (b j))

lemma basisMetricLaplacian_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    basisMetricLaplacian (b.reindex e) B f y = basisMetricLaplacian b B f y := by
  have hf (i : m) : basisMetricFlux (b.reindex e) B f i = basisMetricFlux b B f (e.symm i) := by
    funext z; exact basisMetricFlux_reindex b e B f i z
  simp only [basisMetricLaplacian,basisMetricMatrix_reindex,det_submatrix_equiv_self,hf,
    Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ fderiv ℝ (basisMetricFlux b B f j) y (b j))

end
end Yau.Geometry

end OAI
