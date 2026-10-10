import OAI.Geometry.NodalSets.Elliptic.JacobianCalculus

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourcePrincipal (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (i j : Fin 4) (x : Coord) : ℝ :=
  (ContinuousLinearMap.inverse (g x) (ContinuousLinearMap.proj j)) i

lemma covector_basis (a : Coord →L[ℝ] ℝ) :
    a = ∑ j : Fin 4, a (Pi.single j 1) • (ContinuousLinearMap.proj j : Coord →L[ℝ] ℝ) := by
  ext v
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, mul_comm]

lemma inversePulledForm_covector
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (a : Coord →L[ℝ] ℝ) :
    inversePulledForm g p x (a.comp J.toContinuousLinearMap) =
      J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x)) a) := by
  rw [inversePulledForm_transform g p x hp J hJ]
  congr 2
  ext v
  simp

lemma principal_jacobian_sum
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    ∑ j, chartPrincipal g i j p x * jacobian (rawQuadratic p) x a j =
      (J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x)) (ContinuousLinearMap.proj a))) i := by
  have h := congrArg (fun v : Coord ↦ v i)
    (inversePulledForm_covector g p x hp J hJ (ContinuousLinearMap.proj a))
  conv_lhs at h => rw [covector_basis ((ContinuousLinearMap.proj a).comp J.toContinuousLinearMap)]
  simpa [chartPrincipal,jacobian,hJ,map_sum,map_smul,mul_comm] using h

lemma adjugate_equiv_apply (J : Coord ≃L[ℝ] Coord) (v : Coord) (i : Fin 4) :
    ∑ a, (LinearMap.toMatrix' J.toLinearMap).adjugate i a * v a =
      coordDet J.toContinuousLinearMap * J.symm v i := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ ↦ Matrix.mulVec M (J.symm v) i)
    (Matrix.adjugate_mul (LinearMap.toMatrix' J.toLinearMap))
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  change (LinearMap.toMatrix' J.toLinearMap).adjugate.mulVec (J (J.symm v)) i =
    coordDet J.toContinuousLinearMap * J.symm v i at h
  rw [J.apply_symm_apply] at h
  exact h

theorem determinant_principal_jacobian
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    (jacobian (rawQuadratic p) x).det *
      (∑ j, chartPrincipal g i j p x * jacobian (rawQuadratic p) x a j) =
      ∑ b, (jacobian (rawQuadratic p) x).adjugate i b *
        sourcePrincipal g b a (rawQuadratic p x) := by
  rw [principal_jacobian_sum g p x hp J hJ]
  have hj : jacobian (rawQuadratic p) x = LinearMap.toMatrix' J.toLinearMap := by
    ext b j
    simp [jacobian,hJ,LinearMap.toMatrix'_apply]
  rw [hj]
  exact (adjugate_equiv_apply J
    (ContinuousLinearMap.inverse (g (rawQuadratic p x)) (ContinuousLinearMap.proj a)) i).symm

end
end Yau.Geometry

end OAI
