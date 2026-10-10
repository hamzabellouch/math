import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarSecondOrder
import OAI.Geometry.TamingCompatibility.Charts.CenterLocalJet
import OAI.Geometry.TamingCompatibility.DifferentialForms.FullGreenObservation
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothInverseData
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalKernel
import OAI.Geometry.TamingCompatibility.DifferentialForms.CounterexampleEnergyData
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelCanonical
import OAI.Geometry.TamingCompatibility.Elliptic.ActualPrincipal
import OAI.Geometry.TamingCompatibility.Concentration.ActualHeatResidual
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCompactCutoff
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolventSpatial
import OAI.Geometry.TamingCompatibility.DifferentialForms.CounterexampleMassEnergy
import OAI.Geometry.TamingCompatibility.Concentration.DefectMomentLimit
import OAI.Geometry.TamingCompatibility.Concentration.HodgeResidualEnergy
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAtlasCorrection
import OAI.Geometry.TamingCompatibility.Charts.TripleAtlas

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricHilbert GeometricHilbert.GeometricNormalCharts Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem taming_implies_compatibility
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X]
    (J : AlmostComplexStructure X)
    (h : ∃ α : TwoForm X, IsSymplectic α ∧ Tames α J) :
    ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨α,⟨hs,hc,_⟩,ht⟩ := h
  by_contra hn
  obtain ⟨A,hE,hD,hG⟩ := finite_triple_partition J α hs ht
  let E := fun p : A.centers => parametrixData J α hs ht p.val
  let D := fun p : A.centers => HodgeChart.data J α hs ht p.val
  let G := fun p : A.centers => GeometricChart.data J α hs ht p.val
  obtain ⟨μ,hμ,-,-,hann,-⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  obtain ⟨Q,haQ,hQ,hT,hnormal⟩ := separating_current_L2_correction J α hs ht hc A E hE D hD μ hann
  obtain ⟨S⟩ := concentrationActivationData_nonempty A J α hs ht E hE D hD G hG μ hann Q hT
  have hzero := concentration_forces_correction_zero A J α hs ht E hE D hD μ hann Q haQ hQ hT S
  rw [hzero,inner_zero_left] at hnormal
  norm_num at hnormal
end TamingCompatibility

end
end

end OAI
