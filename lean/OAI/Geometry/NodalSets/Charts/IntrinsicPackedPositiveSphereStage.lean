import OAI.Geometry.NodalSets.Charts.IntrinsicCorrectedChart
import OAI.Geometry.NodalSets.Charts.IntrinsicUniformPositiveSphereStage
import OAI.Geometry.NodalSets.Coefficients.PositiveSphereCorrection
import OAI.Geometry.NodalSets.Elliptic.ExteriorCorrectedEquation
import OAI.Geometry.NodalSets.Elliptic.IntrinsicPackedSmallCorrectedStage
import OAI.Geometry.NodalSets.Elliptic.InverseSquareSmallness
import OAI.Geometry.NodalSets.Elliptic.RoundTensorCoordinateBounds
import OAI.Geometry.NodalSets.Waves.LatticeSphereExtension

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicUniformPositiveSphereStageLocalInst1 intrinsicUniformPositiveSphereStageLocalInst2 intrinsicUniformPositiveSphereStageLocalInst3 intrinsicUniformPositiveSphereStageLocalInst4 intrinsicUniformPositiveSphereStageLocalInst5 intrinsicUniformPositiveSphereStageLocalInst6 intrinsicUniformPositiveSphereStageLocalInst7 intrinsicUniformPositiveSphereStageLocalInst8 intrinsicUniformPositiveSphereStageLocalInst9 intrinsicUniformPositiveSphereStageLocalInst10 intrinsicUniformPositiveSphereStageLocalInst11 intrinsicUniformPositiveSphereStageLocalInst12 intrinsicUniformPositiveSphereStageLocalInst13 intrinsicUniformPositiveSphereStageLocalInst14 intrinsicUniformPositiveSphereStageLocalInst15 intrinsicUniformPositiveSphereStageLocalInst16

theorem intrinsic_packed_positive_sphere_stage :
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
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (J0 : ℕ),
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
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ∧
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
              IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x) ∧
              (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
                (A x+roundTensorPerturbation ag x) w v) ∧
              (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v) ∧
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x) ∧
              (∀ x, 0 < rho x+bg x) ∧ ug ≠ 0 ∧
              (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
                (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
              (∀ x i j k, i ≤ J0 →
                ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
                  seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
              ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K ∪ seedSphereFromCoord '' (Q ∪ Qw) →
                -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
                  (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_small_corrected_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  refine ⟨c,hc,?_⟩
  intro T J0 k0 K'
  obtain ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T J0
  obtain ⟨Qw,hQw,hQwΩ,hext⟩ := literal_lattice_sphere_extension b d.compact_closure_U
    subset_closure (d.compact_closure_U.isBounded.subset subset_closure) d.open_Ω d.closure_U_Ω
  obtain ⟨B,hB,htensor⟩ := round_tensor_coordinate_bound hQ J0
  let D := (1+B)*C
  have hCD : C ≤ D := by dsimp [D]; nlinarith
  obtain ⟨eta,heta,hcorr⟩ := positive_sphere_scalar_correction A hAs hs hp rho hrs hrp
  refine ⟨d,b,hb,D,by dsimp [D]; positivity,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,hext,eventually_inverse_square_small C eta heta,eventually_gt_atTop (0:ℕ)] with n hn hnExt hnSmall hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq⟩ := hn
  obtain ⟨hfin',hExt⟩ := hnExt
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  obtain ⟨ug,hug,hugs,hugval⟩ := hExt coeff hu
  have heps : 0 ≤ C*((n:ℝ)^2)⁻¹ := by positivity
  have hab (x : Yau.Jets.Coord) := hsize x 0 (Nat.zero_le J0)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hab
  obtain ⟨ag,bg,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,hnew,hnewSym,hnewPos,hrnew,hrnewPos⟩ :=
    hcorr _ _ Q hQ halpha hbeta has hbs _ heps hnSmall
      (fun x ↦ (le_add_of_nonneg_right (abs_nonneg _)).trans (hab x))
      (fun x ↦ (le_add_of_nonneg_left (abs_nonneg _)).trans (hab x))
  have hbound : C*((n:ℝ)^2)⁻¹ ≤ D*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hCD (by positivity)
  have hten := htensor _ halpha has ag hagval _ heps
    (fun x i hi ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hsize x i hi))
  have hfixed := corrected_seed_chart_equation A hAs hs hp rho hrp ug hug (seedEigenvalue n)
    ag bg hnew hnewSym hnewPos hrnewPos
  have hfixed' : ∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
      (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x) := by
    apply hfixed
    intro x
    simp_rw [hagval,hbgval,hugval]
    exact heq x
  have hugne : ug ≠ 0 := by
    intro hz
    have h0 : (0 : Yau.Jets.Coord) ∈ seedCoordCube a := by
      constructor <;> intro i <;> simp <;> linarith
    have h0Ω := subset_closure (d.closure_U_Ω (subset_closure (d.C_U (d.inner_C (Or.inl h0)))))
    have hj := hjet 0 h0Ω
    have hzero : (fun x ↦ seedCoordinateField n x + gaussianWaveField
        (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x) =
        (fun _ ↦ (0:ℝ)) := by
      funext x
      rw [← hugval x,hz]
      rfl
    rw [hzero] at hj
    simp [sourceFirstJetSize,sourceEuclideanNorm] at hj
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    have hh : 0 < ((n:ℝ)^65)⁻¹ * max (Real.exp ((n:ℝ)*d.S 0))
        (Real.exp ((n:ℝ)*seedCoordReal 0)) :=
      mul_pos (by positivity) ((Real.exp_pos _).trans_le (le_max_left _ _))
    linarith
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,
    (fun x i hi ↦ (hsize x i hi).trans hbound),heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,
    (fun x ↦ (hagB x).trans hbound),(fun x ↦ (hbgB x).trans hbound),
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed',?_,?_⟩
  · intro x i j k hi
    refine (hten x i j k hi).trans ?_
    have hBD : B*C ≤ D := by dsimp [D]; nlinarith
    calc
      B*(C*((n:ℝ)^2)⁻¹) = (B*C)*((n:ℝ)^2)⁻¹ := by ring
      _ ≤ D*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hBD (by positivity)
  · exact corrected_exterior_equation A rho hK.isClosed
      ((hQ.union hQw).image seedSphereFromCoord_continuous).isClosed hA hrho ag bg ug n
      (hags.trans (image_mono subset_union_left)) (hbgs.trans (image_mono subset_union_left))
      (hugs.trans (image_mono subset_union_right))

end
end Yau.Target

end OAI
