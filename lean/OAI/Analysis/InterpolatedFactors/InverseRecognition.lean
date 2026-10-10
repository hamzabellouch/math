import OAI.Analysis.InterpolatedFactors.DoubleTrace

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_1} {E : Type u_2} {F : Type u_3} {I : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {covariance : I → I → A → A} (X : System A E I covariance) (Y : System A F I covariance)
variable (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
variable (hX : X.normalHull=⊤) (hY : Y.normalHull=⊤)

theorem generatedIso_symm_normal (σ : I → I) :
    @Continuous _ _ (Y.generatedTopology σ) (X.generatedTopology σ)
      (X.generatedIso Y hstate hX hY σ).symm := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (Operator F) := ultraweak F
  let : TopologicalSpace (Y.generated σ) := Y.generatedTopology σ
  apply continuous_induced_rng.mpr
  exact (spatial_normal (X.spatial Y hstate hX hY).symm).comp continuous_subtype_val
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition ReducingSubspace
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]
variable (s : Set (E →L[ℂ] E)) (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

theorem restrictionIso_symm_normal :
    @Continuous _ _ (operatorTopology (reductionImage K s)) (operatorTopology s)
      (restrictionIso K s hps v hvs hpv hvr hvi).symm := by
  let : TopologicalSpace (E →L[ℂ] E) := HilbertUltraweak.topology E
  let : TopologicalSpace (K →L[ℂ] K) := HilbertUltraweak.topology K
  let : TopologicalSpace (bicomm (reductionImage K s)) := operatorTopology (reductionImage K s)
  apply continuous_induced_rng.mpr
  have he : Continuous (fun T : bicomm (reductionImage K s) =>
      K.subtypeL.comp ((T:K →L[ℂ] K).comp K.orthogonalProjectionOnto)) :=
    (HilbertUltraweak.sandwich_continuous K.subtypeL K.orthogonalProjectionOnto).comp continuous_subtype_val
  have hc := HilbertUltraweak.add_continuous he
    ((HilbertUltraweak.sandwich_continuous (star v) v).comp he)
  convert hc using 1
  rfl
end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace FullReducingCorner
variable {A : Type u_6} {E : Type u_7} {I : Type u_8} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)
variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

theorem fullReductionIso_symm_normal :
    @Continuous _ _ (X.reducedSystem.generatedTopology σ) (X.generatedTopology σ)
      (X.fullReductionIso σ v hvs hpv hvr hvi).symm := by
  let : TopologicalSpace (Operator E) := ultraweak E
  let : TopologicalSpace (X.normalHull →L[ℂ] X.normalHull) := ultraweak X.normalHull
  let : TopologicalSpace (X.reducedSystem.generated σ) := X.reducedSystem.generatedTopology σ
  apply continuous_induced_rng.mpr
  have he : Continuous (fun T : X.reducedSystem.generated σ =>
      X.normalHull.subtypeL.comp ((T:X.normalHull →L[ℂ] X.normalHull).comp X.normalHull.orthogonalProjectionOnto)) :=
    (HilbertUltraweak.sandwich_continuous X.normalHull.subtypeL X.normalHull.orthogonalProjectionOnto).comp continuous_subtype_val
  have hc := HilbertUltraweak.add_continuous he
    ((HilbertUltraweak.sandwich_continuous (star v) v).comp he)
  convert hc using 1
  rfl
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
theorem reducedGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip) (reducedGaussianIso u v hv hvu).symm :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_symm_normal scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem fullGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip) (fullGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace ((weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :=
    (weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact ((weightedSystem u v hv hvu).fullReductionIso_symm_normal scalarFlip (pRightEdge u v)
      (pRightEdge_mem_weightedCommutant u v hv hvu) (weightedFull_left u v hv hvu)
      (weightedFull_right u v hv hvu) (weightedFull_initial u v hv hvu)).comp
    (reducedGaussianIso_symm_normal u v hv hvu)

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)
theorem ambientGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      ((ambientSystem u v hu hv' hunit).generatedTopology scalarFlip) (ambientGaussianIso u v hu hv' hunit).symm :=
  (ambientSystem u v hu hv' hunit).generatedIso_symm_normal scalarSystem
    (scalar_ambient_state u v hu hv' hunit)
    (ambientSystem_total u v hu hv' hunit) scalarSystem_total scalarFlip
end FreeGroupFactorMain.WeightedFock

end

end OAI
