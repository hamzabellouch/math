import OAI.Geometry.NodalSets.Charts.GlobalSphereEquation
import OAI.Geometry.NodalSets.Charts.IntrinsicCorrectedChart
import OAI.Geometry.NodalSets.Charts.IntrinsicUniformPositiveSphereStage
import OAI.Geometry.NodalSets.Coefficients.PositiveSphereCorrection
import OAI.Geometry.NodalSets.Elliptic.ExteriorCorrectedEquation
import OAI.Geometry.NodalSets.Elliptic.InverseSquareSmallness
import OAI.Geometry.NodalSets.Elliptic.RoundTensorCoordinateBounds
import OAI.Geometry.NodalSets.Hausdorff.PerturbedNodalTransfer
import OAI.Geometry.NodalSets.Waves.LatticeSphereExtension

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
local instance intrinsicGlobalSphereStageLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicGlobalSphereStageLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicGlobalSphereStageLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance intrinsicGlobalSphereStageLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicGlobalSphereStageLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicGlobalSphereStageLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicGlobalSphereStageLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

theorem intrinsic_global_sphere_stage :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
        (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ rho : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho → (∀ x, 0 < rho x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A rho seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
      (∀ x ∉ K, ∀ v w : AmbientBase,
        ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
        A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) →
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∃ cn > 0, ∀ (T : ℝ) (J0 : ℕ),
      let k0 := max 5 (J0+2)
      let K' := 137*J0+269
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
      ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q Qw : Set Yau.Jets.Coord,
        IsCompact Qw ∧ Qw ⊆ d.Ω ∧
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
            let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
            let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
            let alpha := fun x ↦ f x*u x
            let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ u ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
            tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
            (∀ x i, i ≤ J0 → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
              C*((n:ℝ)^2)⁻¹) ∧
            (∀ x, Yau.weightedDiv roundCoordDensity
              (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x) ∧
            ∃ ug ag bg : Base → ℝ,
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ug ∧
              tsupport (ug-sphericalSeed n) ⊆ seedSphereFromCoord '' Qw ∧
              (∀ x, ug (seedSphereFromCoord x) = u x) ∧
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ag ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ bg ∧
              tsupport ag ⊆ seedSphereFromCoord '' Q ∧ tsupport bg ⊆ seedSphereFromCoord '' Q ∧
              (∀ x, ag (seedSphereFromCoord x) = alpha x) ∧
              (∀ x, bg (seedSphereFromCoord x) = beta x) ∧
              (∀ x, |ag x| ≤ C*((n:ℝ)^2)⁻¹) ∧ (∀ x, |bg x| ≤ C*((n:ℝ)^2)⁻¹) ∧
              ∃ hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x),
              ∃ hnewSym : (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
                (A x+roundTensorPerturbation ag x) w v),
              ∃ hnewPos : (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v),
              ∃ hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x),
              ∃ hrnewPos : (∀ x, 0 < rho x+bg x), ug ≠ 0 ∧
              (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
                (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
              (∀ x i j k, i ≤ J0 →
                ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
                  seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
              (∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
                (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z)) ∧
              ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift ug) ∧ circleLift ug ≠ 0 ∧
              (∀ x : Manifold5, -chartLaplacian
                (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                  (fun x ↦ rho x+bg x) hrnew hrnewPos)
                (extChartAt modelWithCorners x) (circleLift ug) (extChartAt modelWithCorners x x) =
                  seedEigenvalue n*circleLift ug x) ∧
              0 < seedEigenvalue n ∧
              ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
                sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
                nodalMeasure
                  (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                    (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift ug) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_uniform_positive_sphere_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨eta,heta,Cproj,hCproj,htransfer⟩ := uniform_small_correction_nodal_transfer
    A hAs hs hp rho hrs hrp (seedCoordPatch_compactClosure r)
  refine ⟨c,hc,c/(Cproj:ℝ)^4,by positivity,?_⟩
  intro T J0 k0 K'
  obtain ⟨d,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T J0
  refine ⟨d,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,eventually_inverse_square_small C eta heta,eventually_gt_atTop (0:ℕ)] with n hn hnSmall hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hext⟩ := hn
  let := hfin
  have hsource : K ∪ seedSphereFromCoord '' (Q ∪ Qw) ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact seedSpherePatch_closure_in_chart r (subset_closure (hKP hx))
    · exact seedSphereFromCoord_source y
  have hall := intrinsic_global_equation_of_seed_exterior _ hnew hnewSym hnewPos _ ug hug
    (seedEigenvalue n) _ hsource hfixed hext
  have hlift := intrinsic_lift_of_seed_exterior _ hnew hnewSym hnewPos _ ug hug
    (seedEigenvalue n) hrnew hrnewPos hugne _ hsource hfixed hext
  have hm := htransfer ag bg hnew hnewSym hnewPos hrnew hrnewPos
    (fun x ↦ (hagB x).trans hnSmall.le) (fun x ↦ (hbgB x).trans hnSmall.le)
    _ ug d.U
    (fun x hx ↦ subset_closure (d.closure_Ω_patch (subset_closure (d.closure_U_Ω (subset_closure hx)))))
    hugval
  have hnodal := ofReal_le_of_fourth_power_mul_le hCproj (hmeasure.trans hm)
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hall,
    hlift.1,hlift.2.1,hlift.2.2,seedEigenvalue_pos hn0,?_⟩
  simpa only [div_mul_eq_mul_div] using hnodal

end
end Yau.Target

end OAI
