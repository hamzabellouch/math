import OAI.Geometry.EinsteinFour.ChartMetricTransition
import OAI.Geometry.EinsteinFour.CurvatureMetricSkew

namespace OAI

/-! The finite coordinate chain rule used for changes of metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

def jacobianMatrix (F : FourSpace → FourSpace) (z : FourSpace) : Mat4 :=
  fun a i => fderiv ℝ F z (coordinateVector i) a

theorem partialDeriv_comp {F : FourSpace → FourSpace} {f : FourSpace → ℝ}
    {z : FourSpace} (hF : DifferentiableAt ℝ F z)
    (hf : DifferentiableAt ℝ f (F z)) (i : Fin 4) :
    partialDeriv (fun w => f (F w)) i z =
      ∑ a, jacobianMatrix F z a i * partialDeriv f a (F z) := by
  let L : FourSpace →L[ℝ] ℝ := fderiv ℝ f (F z)
  have hc : partialDeriv (fun w => f (F w)) i z =
      L (fderiv ℝ F z (coordinateVector i)) :=
    congrArg (fun D : FourSpace →L[ℝ] ℝ => D (coordinateVector i))
      (hf.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  have hv : fderiv ℝ F z (coordinateVector i) =
      ∑ a, jacobianMatrix F z a i • coordinateVector a :=
    (sum_coordinateVector (fun a => jacobianMatrix F z a i)).symm
  calc
    _ = L (fderiv ℝ F z (coordinateVector i)) := hc
    _ = L (∑ a, jacobianMatrix F z a i • coordinateVector a) := congrArg L hv
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, L, partialDeriv]

theorem jacobian_entry_eq_partial {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : DifferentiableAt ℝ F z) (a i : Fin 4) :
    jacobianMatrix F z a i = partialDeriv (fun w => F w a) i z := by
  have h := ((EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp z
    hF.hasFDerivAt).fderiv
  change _ = fderiv ℝ ((EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ) ∘ F) z
    (coordinateVector i)
  rw [h]
  rfl

theorem jacobian_entry_contDiffAt {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : ContDiffAt ℝ ∞ F z) (a i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => jacobianMatrix F w a i) z := by
  have h := (hF.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := coordinateVector i))
  exact (EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp z h

theorem matrixPartial_comp {F : FourSpace → FourSpace} {A : FourSpace → Mat4}
    {z : FourSpace} (hF : DifferentiableAt ℝ F z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) (F z)) (i : Fin 4) :
    matrixPartial (fun w => A (F w)) i z =
      ∑ a, jacobianMatrix F z a i • matrixPartial A a (F z) := by
  ext r s
  simpa only [matrixPartial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    partialDeriv_comp hF (hA r s) i

theorem jacobian_partials_commute {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : ContDiffAt ℝ ∞ F z) (a i j : Fin 4) :
    partialDeriv (fun w => jacobianMatrix F w a j) i z =
      partialDeriv (fun w => jacobianMatrix F w a i) j z := by
  have hone : ContDiffAt ℝ 1 F z := hF.of_le (by simp)
  have hnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ F w :=
    (hone.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hcongr (r s : Fin 4) :
      partialDeriv (fun w => jacobianMatrix F w a s) r z =
      partialDeriv (fun w => partialDeriv (fun v => F v a) s w) r z := by
    have he : (fun w => jacobianMatrix F w a s) =ᶠ[𝓝 z]
        (fun w => partialDeriv (fun v => F v a) s w) :=
      hnear.mono fun w hw => jacobian_entry_eq_partial hw a s
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector r)) he.fderiv_eq
  rw [hcongr, hcongr]
  have ha : ContDiffAt ℝ ∞ (fun w => F w a) z :=
    (EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp z hF
  have hs := matrixPartial_comm (fun (w : FourSpace) (_ _ : Fin 4) => F w a) z
    (fun _ _ => ha) i j
  exact congrFun (congrFun hs 0) 0

end
end PositiveEinsteinFour.Geometry

end OAI
