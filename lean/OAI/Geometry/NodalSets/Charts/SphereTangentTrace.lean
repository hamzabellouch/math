import Mathlib.Analysis.InnerProductSpace.Laplacian
import OAI.Geometry.NodalSets.Charts.CenteredSphereChart

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

def centeredSphereFrame (p : Base) : Fin 4 ⊕ Fin 1 → AmbientBase :=
  Sum.elim (fun i ↦ centeredSphereIsometry p (EuclideanSpace.basisFun (Fin 4) ℝ i)) (fun _ ↦ p)

lemma centeredSphereFrame_orthonormal (p : Base) : Orthonormal ℝ (centeredSphereFrame p) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · change ⟪centeredSphereIsometry p _,centeredSphereIsometry p _⟫ = _
    rw [(centeredSphereIsometry p).inner_map_map]
    simpa using (EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite i j
  · simp [centeredSphereFrame,centeredSphereIsometry_orthogonal,real_inner_comm]
  · simp [centeredSphereFrame,centeredSphereIsometry_orthogonal]
  · simp [centeredSphereFrame,Subsingleton.elim i j,
      mem_sphere_zero_iff_norm.mp p.property]

def centeredSphereBasis (p : Base) : OrthonormalBasis (Fin 4 ⊕ Fin 1) ℝ AmbientBase :=
  OrthonormalBasis.mk (centeredSphereFrame_orthonormal p)
    ((centeredSphereFrame_orthonormal p).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [AmbientBase])).ge

lemma centeredSphereBasis_apply (p : Base) (i : Fin 4 ⊕ Fin 1) :
    centeredSphereBasis p i = centeredSphereFrame p i := by
  simp [centeredSphereBasis]

lemma sphere_tangent_trace (f : AmbientBase → ℝ) (p : Base) :
    (∑ i, fderiv ℝ (fderiv ℝ f) (p : AmbientBase)
      (centeredSphereIsometry p (EuclideanSpace.basisFun (Fin 4) ℝ i))
      (centeredSphereIsometry p (EuclideanSpace.basisFun (Fin 4) ℝ i))) +
    fderiv ℝ (fderiv ℝ f) (p : AmbientBase) (p : AmbientBase) (p : AmbientBase) =
      Δ f (p : AmbientBase) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (centeredSphereBasis p)]
  simp [Fintype.sum_sum_type,iteratedFDeriv_two_apply,centeredSphereBasis_apply,centeredSphereFrame]

end
end Yau.Target

end OAI
