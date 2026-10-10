import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AlignedFiniteTables
import OAI.GroupTheory.SimpleAmenable.Configurations.FiniteAlignedConfiguration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSectorCompatibility
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ControlCalculus
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateFamilyCompare
import OAI.GroupTheory.SimpleAmenable.CentralCovers.UniformTangentTransport
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PolygonAtomLaw
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AxisSplitting
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SectorDifferenceRange
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AnchorConstants
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GrowthGeneration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ClippedLineSlideAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GlobalSignControl
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveQuadrantAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AllWindowAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConcurrentCellSlopeAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveChartActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentCellDecisions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConstantCellTemplates
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridPrimitiveInputs
import OAI.GroupTheory.SimpleAmenable.RandomFields.FormalLawCovariance
import OAI.GroupTheory.SimpleAmenable.Simplicial.FormalLawReindex
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalSectorSubfamily
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateActualRelators
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ClosedLocalAssignments
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SimultaneousActiveActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateTemplateControl
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InwardMargins
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialGridActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SelectedInwardActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConcurrentCoordinateGates
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveStarCoherence
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ExteriorClippedModels
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FarClippedModels
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ExteriorPhaseGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PhaseClippedModels
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGermActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGlobalTemplates
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GlobalAlignedCentrality
import OAI.GroupTheory.SimpleAmenable.RandomFields.CanonicalPolygonCovariance
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FrameCentrality
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FrameCompatibility
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CommonFrameTransport
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrivateBankFixer
import OAI.GroupTheory.SimpleAmenable.CentralCovers.DistinctSlotFixer
import OAI.GroupTheory.SimpleAmenable.Simplicial.SmallEvenRouting
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CanonicalSlotStars
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationTransport
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GenerationUpstairs
import OAI.GroupTheory.SimpleAmenable.Amenability.LocalBarrierTransport
import OAI.GroupTheory.SimpleAmenable.Amenability.ChartLineTransport
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonVerticalStrings
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonBarFaces
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalEssSurj
import OAI.GroupTheory.SimpleAmenable.Homology.RestrictedPolygon
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageMonoidal
import OAI.GroupTheory.SimpleAmenable.Homology.ProductHomologyMaps
import OAI.GroupTheory.SimpleAmenable.Homology.FiberSumHomology
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleAllNatural
import OAI.GroupTheory.SimpleAmenable.Simplicial.RegularBlockFaces
import OAI.GroupTheory.SimpleAmenable.Simplicial.PointFiberMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.CellMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.TranslationFiberMonoidal
import OAI.GroupTheory.SimpleAmenable.Homology.RegularTotalFiniteDifferentials
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricComponents
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarBinaryBoundary

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable
open FreeChains IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2

lemma polygon_triple_homology_finite (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤5) :
    Module.Finite ℤ ((bar₃ (C:=PolygonObject a)).homology Z n:A) := by
  apply PolygonObject.LabelledStage.polygon_bar₃_finite_of_symmetric a ha _ n hn
  intro q _ hq
  exact SymmetricConfiguration.triple_homology_finite q hq

lemma polygon_bar_homology_finite (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤3) :
    Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z n:A) :=
  bar_finite_of_triple (polygon_triple_homology_finite a ha) n hn

lemma polygon_full_low_homology_finite (a m:ℕ) (ha:0<a) (hm : 34 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ∧
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) := by
  have barH1Finite := polygon_bar_homology_finite a ha 1 (by omega)
  have barH2Finite := polygon_bar_homology_finite a ha 2 (by omega)
  have barH3Finite := polygon_bar_homology_finite a ha 3 (by omega)
  exact ⟨PolygonTracks.fullH1_finite_of_bar a m (by omega),
    PolygonTracks.fullH2_finite_of_bar a m hm⟩

lemma polygon_alternating_H2_finite (a m:ℕ) (ha:0<a) (hm : 205 < m) :
    Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m))) := by
  obtain ⟨fullH1Finite,fullH2Finite⟩:=polygon_full_low_homology_finite a m ha (by omega)
  exact PolygonTracks.finite_alternating_H2_of_full a m hm

theorem main : ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G := by
  obtain ⟨a,ha,h⟩:=fixed_track_polygon_progress
  obtain ⟨hinfinite,hsimple,hfolner,H,hH,q,hpres,hsur,hcentral⟩:=h 206 (by omega)
  let:=hH
  have:=hpres
  have:=polygonAlternatingGroup_perfect a 206 (by omega)
  have:=polygon_alternating_H2_finite a 206 ha (by omega)
  exact ⟨polygonAlternatingGroup a 206,inferInstance,hinfinite,
    finitelyPresented_of_central_cover_h2 q hsur hcentral,hsimple,hfolner⟩
end SimpleAmenable

end

end OAI
