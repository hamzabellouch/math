import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoundarySmooth
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Manifold Bundle Function
open scoped ContDiff Topology
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

lemma cutInclusion_smooth [IsManifold I3 ∞ N] (D : OuterDomain N) :
    ContMDiff I2 I3 ∞ (cutInclusion D) :=
  D.embedding.isImmersion.contMDiff.comp CKSBoundarySurface.inclusion_smooth

lemma cutInclusion_derivative_injective [IsManifold I3 ∞ N] (D : OuterDomain N) (x : Surface D) :
    Injective (mfderiv I2 I3 (cutInclusion D) x) := by
  unfold cutInclusion
  rw [mfderiv_comp x ((D.embedding.isImmersion.contMDiff x.val).mdifferentiableAt (by simp))
    ((CKSBoundarySurface.inclusion_smooth x).mdifferentiableAt (by simp))]
  · change Injective ((mfderiv I3 I3 D.inclusion x.val) ∘
      (mfderiv I2 I3 (Subtype.val : Surface D → D.Carrier) x))
    exact (CKSEmbeddingDerivative.smooth_embedding_derivative_injective D.embedding x.val).comp
      (CKSBoundarySurface.inclusion_mfderiv_injective x)

lemma cutInclusion_embedding [IsManifold I3 ∞ N] (D : OuterDomain N) :
    Topology.IsEmbedding (cutInclusion D) :=
  D.embedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal

lemma cutInclusion_range [IsManifold I3 ∞ N] (D : OuterDomain N) :
    range (cutInclusion D) = D.cut := by
  simp only [cutInclusion,range_comp,Subtype.range_coe,OuterDomain.cut,Surface,Boundary]

variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

instance surfaceCompact (D : OuterDomain N) : CompactSpace (Surface D) := by
  apply isCompact_iff_compactSpace.mp
  exact D.embedding.isEmbedding.isCompact_iff.mpr D.compact_boundary

instance surfaceT2 [T2Space N] (D : OuterDomain N) : T2Space (Surface D) :=
  (cutInclusion_embedding D).t2Space

end CKSFullCutArea

end

end OAI
