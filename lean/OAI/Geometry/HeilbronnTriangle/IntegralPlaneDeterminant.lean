import OAI.Geometry.HeilbronnTriangle.LatticeSplit
import OAI.Geometry.HeilbronnTriangle.PlaneCovolume

namespace OAI


noncomputable section

namespace Problem355.Lattice

open Module
open scoped Matrix

theorem abs_det_kernel_basis_extension
    (L : Submodule ℤ (Fin 3 → ℤ)) (f : L →ₗ[ℤ] ℤ)
    (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : L) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![(fun j => (((b 0 : L) : Fin 3 → ℤ) j : ℝ)),
      (fun j => (((b 1 : L) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((u : Fin 3 → ℤ) j : ℝ))]| = (L.toAddSubgroup.index : ℝ) := by
  simpa only [LatticeSplit.extendIntegerKernelBasis_inl,
    LatticeSplit.extendIntegerKernelBasis_inr] using
    abs_det_sum_basis_eq_index L
      (LatticeSplit.extendIntegerKernelBasis f g hg hdiv u hu b)

theorem abs_det_sum_basis_eq_one
    (b : Basis (Fin 2 ⊕ Unit) ℤ (Fin 3 → ℤ)) :
    |Matrix.det ![(fun j => (b (Sum.inl 0) j : ℝ)),
      (fun j => (b (Sum.inl 1) j : ℝ)),
      (fun j => (b (Sum.inr ()) j : ℝ))]| = 1 := by
  let bt : Basis (Fin 2 ⊕ Unit) ℤ (⊤ : Submodule ℤ (Fin 3 → ℤ)) :=
    b.map Submodule.topEquiv.symm
  simpa [bt] using abs_det_sum_basis_eq_index (⊤ : Submodule ℤ (Fin 3 → ℤ)) bt

theorem abs_det_primitive_kernel_basis_extension
    (f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ) (u : Fin 3 → ℤ) (hu : f u = 1)
    (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![(fun j => ((b 0 : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b 1 : Fin 3 → ℤ) j : ℝ)), (fun j => (u j : ℝ))]| = 1 := by
  simpa only [LatticeSplit.extendKernelBasis_inl,
    LatticeSplit.extendKernelBasis_inr] using
    abs_det_sum_basis_eq_one (LatticeSplit.extendKernelBasis f u hu b)

end Problem355.Lattice

end

end OAI
