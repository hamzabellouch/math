import OAI.Geometry.Relativity.CKS.SourceGeometry
import OAI.Geometry.Relativity.CKS.SourceBalancedChart
import OAI.Geometry.Relativity.CKS.SourceTopology
import OAI.Geometry.Relativity.CKS.IntrinsicReplacementWithChart
import OAI.Geometry.Relativity.CKS.SourceReplacementDefinitions

namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle Filter CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSADM (Symbol)
open scoped ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
attribute [local instance] manifold_regular

theorem area_controlled_end_replacement
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (_hOrient : Orientable (N := N))
    (hScompact : IsCompact (I3.boundary N)) (_hSnonempty : (I3.boundary N).Nonempty)
    (hcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (hDEC : PhysicalDEC I3 g.inner K)
    (d : CKSData g K)
    (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1) :
    ∃ (d' : CKSData g K) (R₀ : ℝ) (ε : ℝ → ℝ),
      bondiCharge d'.massAspect =
        (Real.sqrt ((bondiCharge d.massAspect).1^2 - ‖(bondiCharge d.massAspect).2‖^2),0) ∧
      d'.chart.radius < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      CKSFullCutArea.minEnclosingArea g < ⊤ ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (gR : SmoothMetric I3 (M := N)) (kR : InnerField I3 (M := N))
          (G k : SpatialTensor) (η : ℝ),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 kR) ∧
          (∀ x v w, kR x v w = kR x w v) ∧
          (∀ x, x ∉ d'.chart.domain ∨ ‖d'.chart.coordinate x‖ ≤ R →
            gR.inner x = g.inner x ∧ kR x = K x) ∧
          PhysicalDEC I3 gR.inner kR ∧
          (∀ x v, (1-ε R) * g.inner x v v ≤ gR.inner x v v) ∧
          CKSReplacementCompleteness.IsComplete I3 gR.toContinuousRiemannianMetric ∧
          constraintsIntegrable gR kR ∧
          (∀ x ∈ d'.chart.domain,
            gR.inner x = endInner I3 d'.chart.coordinate G x ∧
            kR x = endInner I3 d'.chart.coordinate k x) ∧
          (∀ i j : Fin 3, Symbol 1
            (fun x => spatialCartesian G x i j - (if i=j then 1 else 0))) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k x = 0) ∧
          Tendsto (spatialADMEnergy G) atTop
            (𝓝 (Real.sqrt ((bondiCharge d.massAspect).1^2 - ‖(bondiCharge d.massAspect).2‖^2) + η)) ∧
          Tendsto (spatialADMMomentum G k) atTop (𝓝 0) ∧
          0 ≤ η ∧ η ≤ 2 * R ^ (-(1/2 : ℝ)) ∧
          CKSFullCutArea.minEnclosingArea gR < ⊤ ∧
          (1-ε R) * minimumEnclosingArea g ≤ minimumEnclosingArea gR ∧
          ∀ D : OuterDomain N,
            CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area gR D < ⊤ ∧
            (1-ε R) * cutArea g D ≤ cutArea gR D
 := by
  classical
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  obtain ⟨hA,hB,hpos,hdDEC⟩ := CKSData.source_geometry g K hKsym hDEC d
  obtain ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hVo,hfs,his,hleft,hright,hclosed,hcompact,hout⟩ :=
    original_CKS_replacement_intrinsic_chart_package d.aspect_smooth ht
      d.metricPerturbation d.tensorPerturbation d.patches d.covers d.aspect_eq d.realizes
      d.chart.radius_pos d.metric_smooth d.tensor_smooth hA hB hpos hdDEC
      g K hK hKsym hDEC hcomplete d.chart.coordinate d.chart.isOpen d.chart.smooth
      d.chart.closed_far_side d.chart.inverse d.chart.inverse_smooth
      d.chart.left_inverse d.chart.right_inverse d.chart.compact_inner_side d.represents
      (C := ∅) isCompact_empty
  let H := hyperbolicHomeomorph (bondiCharge d.massAspect).1 (bondiCharge d.massAspect).2 ht
  let f' := H.symm ∘ d.chart.coordinate
  let c : CoordinateEnd (N := N) := {
    radius := T
    radius_pos := hT
    domain := {x | x ∈ d.chart.domain ∧ T < ‖f' x‖}
    isOpen := hVo
    coordinate := f'
    inverse := d.chart.inverse ∘ H
    smooth := hfs
    inverse_smooth := his
    mapsTo := fun x hx => hx.2
    left_inverse := hleft
    right_inverse := hright
    closed_far_side := hclosed
    compact_inner_side := fun r hr => hcompact r hr.le }
  obtain ⟨d',hd',hM',hcharge⟩ := CKSData.balanced_in_chart g K d ht c
    (fun x hx => hx.1) rfl
  have hgfinite := CKSFullCutArea.minEnclosingArea_finite g hScompact
  refine ⟨d',R₀,ε,hcharge,?_,hR₀,hε,hgfinite,?_⟩
  · rw [hd']
    exact hTR
  · intro R hR
    obtain ⟨heps,gR,kR,hks,hksym,hgDEC,hgcomplete,hC,hold,hlower,harea,hrep,
      hkzero,hAF,hE,hP,hη0,hη1,hendint,hmomzero,hint,hindarea,hcutarea⟩ := hout R hR
    have hc : 0 ≤ 1-ε R := sub_nonneg.mpr heps.2.le
    have hgRfinite := CKSFullCutArea.minEnclosingArea_finite gR hScompact
    refine ⟨heps,gR,kR,G R,k R,CKSBending.paddingCharge R,hks,hksym,?_,hgDEC,hlower,
      hgcomplete,hint,?_,hAF,hkzero,hE,hP,hη0,?_,hgRfinite,?_,?_⟩
    · simpa only [hd'] using hold
    · intro x hx
      rw [hd'] at hx ⊢
      exact hrep x hx
    · have hRpos : 0 < R := lt_of_lt_of_le (by linarith : 0 < R₀) hR
      rw [Real.rpow_neg hRpos.le,← Real.sqrt_eq_rpow]
      simpa only [div_eq_mul_inv] using hη1
    · have h := ENNReal.toReal_mono (ne_of_lt hgRfinite) hindarea
      simpa only [minimumEnclosingArea_eq_toReal,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using h
    · intro D
      obtain ⟨hD,hDR,hDa⟩ := hcutarea D
      refine ⟨hD,hDR,?_⟩
      have h := ENNReal.toReal_mono (ne_of_lt hDR) hDa
      simpa only [cutArea,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using h

end
end CKSSourceExterior

end

end OAI
