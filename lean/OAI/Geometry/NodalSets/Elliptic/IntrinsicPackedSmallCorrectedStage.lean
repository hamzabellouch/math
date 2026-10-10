import OAI.Geometry.NodalSets.Coefficients.IntrinsicCorrectionSize
import OAI.Geometry.NodalSets.Elliptic.IntrinsicPackedSelectedStage
import OAI.Geometry.NodalSets.Elliptic.LiteralSeededFieldBounds

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_packed_small_corrected_stage :
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
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Yau.Jets.Coord,
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
            ∀ x, Yau.weightedDiv roundCoordDensity
              (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_selected_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  refine ⟨c,hc,?_⟩
  intro T J0 k0 K'
  have hk0 : 5 ≤ k0 := le_max_left _ _
  have hJ : J0+2 ≤ k0 := le_max_right _ _
  obtain ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T k0 K' hk0
  have hQB : Q ⊆ seedCoordBranch := hQΩ.trans (subset_closure.trans d.closure_Ω_branch)
  obtain ⟨F,hF,hfield⟩ := literal_seeded_lattice_field_bound b subset_closure (d.compact_closure_U.isBounded.subset subset_closure) hQ hQB
  obtain ⟨B,hB,hcorr⟩ := intrinsic_real_correction_size A rho hrs hQ J0 hF
  refine ⟨d,b,hb,B*C,by positivity,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,hfield,eventually_gt_atTop (0:ℕ)] with n hn hnfield hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hR,hadd,hsup,hzero,hRb,hjet,hmeasure,hpacking⟩ := hn
  obtain ⟨hfin',hfbound⟩ := hnfield
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  obtain ⟨_,hub⟩ := hfbound coeff hcoeff
  let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
  let H := fun x ↦ max (Real.exp ((n:ℝ)*d.S x)) (Real.exp ((n:ℝ)*seedCoordReal x))
  have hH (x : Yau.Jets.Coord) : 0 < H x := (Real.exp_pos _).trans_le (le_max_left _ _)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  let eps : ℝ := C*(n:ℝ)^(-(K':ℝ))
  have heps : 0 < eps := mul_pos hC (Real.rpow_pos_of_pos hnpos _)
  have hres : ∀ x, DerivativeBound (J0+1)
      (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n) u)
      x (eps*H x) := by
    intro x i hi
    exact (hRb x i (by omega)).trans (by
      change C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x) ≤ eps*H x
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) heps.le)
  have huf (x : Yau.Jets.Coord) (hx : x ∈ Q) (i : ℕ) (hi : i ≤ J0+2) :=
    hub x hx (⟨i,by omega⟩ : Fin (k0+1))
  obtain ⟨hf,halpha,hbeta,has,hbs,hsize,heq⟩ := hcorr u H hu hH n hn0 eps heps hR hsup hres huf
    (fun x hx ↦ hjet x (subset_closure (hQΩ hx)))
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,?_,heq⟩
  intro x i hi
  refine (hsize x i hi).trans_eq ?_
  dsimp [eps,K']
  rw [Real.rpow_neg hnpos.le,Real.rpow_natCast]
  have he : 137*J0+269 = (137*J0+267)+2 := by omega
  rw [he,pow_add]
  field_simp

end
end Yau.Target

end OAI
