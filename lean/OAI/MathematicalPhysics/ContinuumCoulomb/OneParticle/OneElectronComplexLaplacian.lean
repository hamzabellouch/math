import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorDifferential
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedResidualPairing

namespace OAI

/-! The one-electron coordinate isometry identifies the physical complex
Laplacian with the Laplacian already used for the manufactured real orbitals. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem configurationComplexPartial_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 1 f) (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => (f y:ℂ)) a x =
      (configurationRealPartial f a x:ℂ) := by
  exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1))
    (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem configurationComplexLaplacian_ofReal {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Configuration n) :
    configurationComplexLaplacian (fun y => (f y:ℂ)) x =
      (configurationRealLaplacian f x:ℂ) := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => (f y:ℂ)) a =
        (fun y => (configurationRealPartial f a y:ℂ)) :=
    funext (configurationComplexPartial_ofReal f (hf.of_le (by norm_num)) a)
  simp only [configurationComplexLaplacian,hfirst,
    configurationComplexPartial_ofReal _ (configurationRealPartial_C1 hf _),
    configurationRealLaplacian,Complex.ofReal_sum]

theorem oneElectron_complex_partial (f : Position → ℂ) (hf : ContDiff ℝ 1 f)
    (b : Fin 3) (x : Configuration 1) :
    configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) x =
      positionComplexPartial f b (oneElectronCoordinates x) := by
  have h := (hf.differentiable (by norm_num) (oneElectronCoordinates x)).hasFDerivAt.comp x
    oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  simpa only [configurationComplexPartial,positionComplexPartial,Function.comp_def,
    ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,oneElectronCoordinates_single] using
      congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (EuclideanSpace.single (0,b) 1)) h.fderiv

theorem oneElectron_complex_laplacian (f : Position → ℂ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationComplexLaplacian (fun y => f (oneElectronCoordinates y)) x =
      positionComplexLaplacian f (oneElectronCoordinates x) := by
  have hfirst (b : Fin 3) :
      configurationComplexPartial (fun y => f (oneElectronCoordinates y)) (0,b) =
        (fun y => positionComplexPartial f b (oneElectronCoordinates y)) :=
    funext (oneElectron_complex_partial f (hf.of_le (by norm_num)) b)
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type,Fin.sum_univ_one]
  simp only [hfirst,oneElectron_complex_partial _ (positionComplexPartial_C1 f hf _),
    positionComplexLaplacian]

theorem correctedManufacturedResidual_complex_laplacian {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Position) :
    (correctedManufacturedResidual rho H S freq scale u i x:ℂ) =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => (correctedLocalizedMode freq u i y:ℂ)) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*(correctedLocalizedMode freq u i x:ℂ)-
      (((-1/2:ℝ)+freq/2):ℂ)*(correctedLocalizedMode freq u i x:ℂ) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u i) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)
  have hx := correctedManufacturedResidual_eq hrelation H S scale u i (oneElectronCoordinates.symm x)
  have hL := oneElectron_complex_laplacian (fun y => (correctedLocalizedMode freq u i y:ℂ))
    (Complex.ofRealCLM.contDiff.comp hf) (oneElectronCoordinates.symm x)
  change configurationComplexLaplacian (fun y => (oneElectronCorrectedMode freq u i y:ℂ))
    (oneElectronCoordinates.symm x) = _ at hL
  rw [configurationComplexLaplacian_ofReal _ (oneElectronCorrectedMode_C2 freq u i)] at hL
  simp only [LinearIsometryEquiv.apply_symm_apply] at hx hL
  rw [← hL, hx]
  simp only [oneElectronCorrectedMode,LinearIsometryEquiv.apply_symm_apply]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
