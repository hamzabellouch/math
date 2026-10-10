import OAI.Geometry.Relativity.CKS.IntrinsicEndChart
import OAI.Geometry.Relativity.CKS.CutArea
import OAI.Geometry.Relativity.CKS.ConstraintPhysicalNormalization

namespace OAI

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter MeasureTheory CKSLorentz CKSMetricGluing CKSGeometricCuts
open CKSSphericalHarmonics CKSADM CKSBending
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]

theorem original_CKS_replacement_intrinsic_chart_package
    {M : CKSLorentz.Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : CKSLorentz.Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hgDEC : PhysicalDEC I3 g.inner K)
    (hgcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (f : N → E) {U : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (finv : E → N)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f (sourceSpatial A) x ∧
      K x = endInner I3 f (sourceSpatial B) x)
    {C : Set N} (hC : IsCompact C) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let H := hyperbolicHomeomorph e p ht
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      0 < T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
      (∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r}) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (g' : SmoothMetric I3 (M := N)) (K' : InnerField I3 (M := N)),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
          (∀ x v w, K' x v w = K' x w v) ∧
          PhysicalDEC I3 g'.inner K' ∧
          CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric ∧
          (∀ x ∈ C, g'.inner x = g.inner x ∧ K' x = K x) ∧
          (∀ x, x ∉ V ∨ ‖f' x‖ ≤ R → g'.inner x = g.inner x ∧ K' x = K x) ∧
          CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric (ε R) ∧
          ENNReal.ofReal (1-ε R)*minEnclosingArea N g.toContinuousRiemannianMetric ≤
            minEnclosingArea N g'.toContinuousRiemannianMetric ∧
          (∀ x, x ∈ U ∧ T < ‖f' x‖ →
            g'.inner x = endInner I3 f' (G R) x ∧ K' x = endInner I3 f' (k R) x) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
          (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
          Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
          Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
          0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
          (∀ s : ℝ, T < s →
            IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
            IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
              (CKSAngularGeometry.physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
              (CKSAngularGeometry.physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
              (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0) ∧
          CKSIntrinsicConstraints.IntegrableConstraints g' K' ∧
          ENNReal.ofReal (1-ε R) * CKSFullCutArea.minEnclosingArea g ≤
            CKSFullCutArea.minEnclosingArea g' ∧
          ∀ D : OuterDomain N,
            CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area g' D < ⊤ ∧
            ENNReal.ofReal (1-ε R) * CKSFullCutArea.area g D ≤ CKSFullCutArea.area g' D := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let H := hyperbolicHomeomorph e p ht
  let f' := H.symm ∘ f
  let A' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
  let B' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)
  obtain ⟨T₀,Q,ε,G,k,hT₀,hTQ,hQ,hε,hfar,hend⟩ :=
    original_CKS_end_integrable_replacement hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  obtain ⟨T,hT,hT₀T,hVo,hfsV,hiV,hleftV,hrightV,hVclosed,hVcompact⟩ :=
    boosted_exterior_coordinates ht f finv hU hf hi hleft hright hclosed hcompact T₀
  let V : Set N := {x | x ∈ U ∧ T < ‖f' x‖}
  have hVopen : IsOpen V := hVo
  have hVc : ∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖} := hVclosed
  have hfs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H.symm :=
    (hyperbolicMap_smooth e (mass e p) (-p)).contMDiff
  have hf' : ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V :=
    (hfs.comp_contMDiffOn hf).mono (fun x hx => hx.1)
  have hVtail : ∀ x ∈ V, T < ‖f' x‖ := fun x hx => hx.2
  have hsame : ∀ x ∈ V, g.inner x = endInner I3 f' A' x ∧ K x = endInner I3 f' B' x := by
    intro x hx
    have hsx := hf.contMDiffAt (hU.mem_nhds hx.1)
    exact ⟨(hsource x hx.1).1.trans (endInner_balanced ht f A hsx).symm,
      (hsource x hx.1).2.trans (endInner_balanced ht f B hsx).symm⟩
  obtain ⟨D,hD,hDC⟩ := compact_side_eventually f' hVc hC
  let R₀ := max Q (max (T+1) D)
  have hQR : Q ≤ R₀ := le_max_left _ _
  have hTR : T < R₀ := lt_of_lt_of_le (by linarith : T < T+1)
    ((le_max_left _ _).trans (le_max_right _ _))
  have hDR : D ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,R₀,ε,G,k,hT,hTR,hQ.trans hQR,hε,hVopen,hfsV,hiV,hleftV,hrightV,hVc,hVcompact,?_⟩
  intro R hR
  obtain ⟨heps,hGs,hks,hgeom,holdR,hzero,hAF,hE,hP,hpad0,hpad1,hint,hmom⟩ := hend R (hQR.trans hR)
  have hGs' := hGs.mono (fun x hx => hT₀T.trans_lt hx)
  have hks' := hks.mono (fun x hx => hT₀T.trans_lt hx)
  have hgeom' (x : E) (hx : T < ‖x‖) := hgeom x (hT₀T.trans_lt hx)
  obtain ⟨g',K',hK',hKsym',hnew,hold',hlower,hcomplete,harea⟩ :=
    extend_actual_end g K hK hKsym f' hVopen hf' hVtail hVc A' B' (G R) (k R)
      hsame (hTR.trans_le hR) heps.1 hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      holdR (fun x hx => (hgeom' x hx).2.2.2.2)
  have hDECall : PhysicalDEC I3 g'.inner K' :=
    extended_manifold_DEC g g' K K' hgDEC f' hVopen (hTR.trans_le hR) hf' hVtail hVc
      (G R) (k R) hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      (fun x hx => (hgeom' x hx).2.2.2.1) hnew hold'
  have hintglobal : CKSIntrinsicConstraints.IntegrableConstraints g' K' := by
    apply CKSIntrinsicConstraints.physical_normalization
    exact CKSIntrinsicConstraints.global_constraints_from_end g' K' hDECall f' (finv ∘ H)
      (show T < T+1 by linarith) hVopen hf' hiV hleftV hrightV
      (hVcompact (T+1) (by linarith)) (G R) (k R) hGs' hks'
      (fun x hx => ⟨(hgeom' x hx).1,(hgeom' x hx).2.1⟩)
      (fun x hx => (hgeom' x hx).2.2.1) hnew
      (hint (T+1) (hT₀T.trans_lt (by linarith))).1
      (hint (T+1) (hT₀T.trans_lt (by linarith))).2
  have hindarea := CKSFullCutArea.minEnclosingArea_lower g g' (sub_nonneg.mpr heps.2.le) hlower
  have hcutarea (D : OuterDomain N) := CKSFullCutArea.area_lower g g'
    (sub_nonneg.mpr heps.2.le) hlower D
  refine ⟨heps,g',K',hK',hKsym',hDECall,hcomplete heps.2 hgcomplete,?_,
    hold',hlower,harea heps.2,hnew,hzero,hAF,hE,hP,hpad0,hpad1,
    (fun s hs => hint s (hT₀T.trans_lt hs)),hmom,hintglobal,hindarea,
    (fun D => ⟨CKSFullCutArea.area_finite g D,CKSFullCutArea.area_finite g' D,hcutarea D⟩)⟩
  intro x hx
  exact hold' x (hDC R (hDR.trans hR) x hx)
end
end CKSSpatialManifold

end

end OAI
