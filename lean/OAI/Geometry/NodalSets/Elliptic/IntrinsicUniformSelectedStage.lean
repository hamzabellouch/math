import OAI.Geometry.NodalSets.Coefficients.IntrinsicTotalResidual
import OAI.Geometry.NodalSets.Elliptic.IntrinsicNoncriticalPlacement
import OAI.Geometry.NodalSets.Hausdorff.FixedDomainPlacedNodal

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_uniform_selected_stage :
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
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (k0 K' : ℕ), 5 ≤ k0 →
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
    ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧
            ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (∀ x : Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | u y.1 = 0}) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := intrinsic_noncritical_placed_data
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hρ
  have hreg := intrinsicSeedCoordMetric_regular A hAs hs hp rho hrs hrp
  obtain ⟨c,hc,hcertAll⟩ := fixed_domain_literal_nodal_certificate
    (intrinsicSeedCoordMetric A rho) (seedCoordPatch_compactClosure r)
    hreg.1.continuous.continuousOn (fun y _ ↦ hreg.2.2 y)
  refine ⟨c,hc,?_⟩
  intro T k0 K' hk0
  have hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source :=
    hKP.trans (subset_closure.trans (seedSpherePatch_closure_in_chart r))
  obtain ⟨d⟩ := hplace A hAs hs hp rho hrs hrp hclose (seedDeviationCoordinates K)
    (seedDeviationCoordinates_compact hK hchart) (seedDeviationCoordinates_subset_patch hKP) T
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hres⟩ :=
    intrinsic_placed_total_residual A hAs hs hp rho hrs hrp d ha.le hK hchart hA hρ k0 K'
  have hcube : seedCoordCube a ⊆ d.U := fun x hx ↦ d.C_U (d.inner_C (Or.inl hx))
  have hvolume : MeasureTheory.volume (seedCoordCube a) ≠ 0 := by
    simp only [seedCoordCube,Real.volume_Icc_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    apply pow_ne_zero
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hcert := hcertAll d b
    (d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans subset_closure))) hk0
    (fun x hx ↦ hq x (subset_closure (d.closure_Ω_patch hx)))
    (show IsCompact (seedCoordCube a) from isCompact_Icc) hcube d.gap_pos
    (fun x hx ↦ d.inner_gap x (Or.inl hx)) hvolume
  refine ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hres,hcert] with n hn hc
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',coeff,hcoeff,hf,hjet,hmeasure⟩ := hc
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  have hr := hn coeff
  exact ⟨hfin,coeff,hcoeff,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,
    hr.2.2.2.2.1,hr.2.2.2.2.2 hcoeff,hjet,hmeasure⟩

end
end Yau.Target

end OAI
