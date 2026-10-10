import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.FiniteMatrixLimit
import OAI.Analysis.JiangSu.TensorProducts.NonUnitalCStarCompletion
import OAI.Analysis.JiangSu.TraceCone.FamilyQuotient
import OAI.Analysis.JiangSu.DimensionFunctions.FiniteSpectralIntegralContinuity
import OAI.Analysis.JiangSu.CuntzSemigroup.QuasitraceFamily
import OAI.Analysis.JiangSu.TensorProducts.CanonicalSpatial
import OAI.Analysis.JiangSu.CentralSequences.MatrixCompressionCentrality
import OAI.Analysis.JiangSu.Comparison.ScalarStrictComparison
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedRankExhaustion
import OAI.Analysis.JiangSu.Nonunital.CuntzAlmostUnperforation
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCStarInductiveLimit
import OAI.Analysis.JiangSu.CStarAlgebras.ConcreteIterateDiagonalization
import OAI.Analysis.JiangSu.CStarAlgebras.ConnectedStageReduction
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropEndpointGenerators
import OAI.Analysis.JiangSu.DimensionDrop.ToeplitzDimensionDrop
import OAI.Analysis.JiangSu.Traceless.EmptyTraceComparisonBridge
import OAI.Analysis.JiangSu.DimensionDrop.SequentialProjectionless
import OAI.Analysis.JiangSu.DimensionDrop.PresentationCertificate

namespace OAI

noncomputable section
namespace OriginalJiangSu.Main
open Pureness CurrentMain Filter
open scoped CStarAlgebra

abbrev UnitalSpatialEquiv
    (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    : Type :=
    let tensor := @ActualSpatial.Tensor A OriginalJiangSu.Algebra
      (inferInstance : CStarAlgebra A)
      (@SequentialCStar.System.instCStarAlgebraSubtypeFamilyQuotientMemStarSubalgebraComplexLimit
        OriginalJiangSu.Stage
        (fun index =>
          JiangSuConstruction.instCStarAlgebraSubtypeContinuousMapElemRealIntervalTensorMatMemStarSubalgebraComplexDimensionDrop
            (OriginalJiangSu.pair index).p (OriginalJiangSu.pair index).q)
        OriginalJiangSu.stageNontrivial OriginalJiangSu.system)
      (inferInstance : PartialOrder A)
      (inferInstance : StarOrderedRing A)
      OriginalJiangSu.algebraOrder
      OriginalJiangSu.algebraStarOrder
    @StarAlgEquiv ℂ A tensor
      (inferInstance : Add A)
      (AddMemClass.add tensor)
      (inferInstance : Mul A)
      (MulMemClass.mul tensor)
      (inferInstance : SMul ℂ A)
      (SetLike.smul tensor)
      (inferInstance : Star A)
      (StarMemClass.instStar tensor)

theorem nonunitalSpatial_addMemClass
    (A D : Type) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] :
    AddMemClass
      (NonUnitalStarSubalgebra ℂ (ActualSpatial.Tensor (Unitization ℂ A) D))
      (ActualSpatial.Tensor (Unitization ℂ A) D) := inferInstance

theorem nonunitalSpatial_mulMemClass
    (A D : Type) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] :
    MulMemClass
      (NonUnitalStarSubalgebra ℂ (ActualSpatial.Tensor (Unitization ℂ A) D))
      (ActualSpatial.Tensor (Unitization ℂ A) D) := inferInstance

theorem nonunitalSpatial_smulMemClass
    (A D : Type) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] :
    SMulMemClass
      (NonUnitalStarSubalgebra ℂ (ActualSpatial.Tensor (Unitization ℂ A) D)) ℂ
      (ActualSpatial.Tensor (Unitization ℂ A) D) := inferInstance

theorem nonunitalSpatial_starMemClass
    (A D : Type) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] :
    StarMemClass
      (NonUnitalStarSubalgebra ℂ (ActualSpatial.Tensor (Unitization ℂ A) D))
      (ActualSpatial.Tensor (Unitization ℂ A) D) := inferInstance

abbrev SpatialIdealEquiv
    (A E : Type) [NonUnitalCStarAlgebra A]
    [NonUnitalNonAssocSemiring E] [Module ℂ E] [Star E]
    (ideal : NonUnitalStarSubalgebra ℂ E) : Type :=
    @StarAlgEquiv ℂ A ideal
      (inferInstance : Add A)
      (AddMemClass.add ideal)
      (inferInstance : Mul A)
      (MulMemClass.mul ideal)
      (inferInstance : SMul ℂ A)
      (SetLike.smul ideal)
      (inferInstance : Star A)
      (StarMemClass.instStar ideal)

abbrev NonunitalSpatialEquivCore
    (A D : Type) [algebra : NonUnitalCStarAlgebra A] [dCStar : CStarAlgebra D]
    [dOrder : PartialOrder D] [dStarOrder : StarOrderedRing D] : Type :=
    A ≃⋆ₐ[ℂ] (@ActualSpatial.NonunitalTensor A D algebra dCStar dOrder dStarOrder)

private theorem unitalSpatialEquiv_of_nonempty
    (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (absorption : Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.Tensor A OriginalJiangSu.Algebra)) :
    Nonempty (UnitalSpatialEquiv A) := by
  exact absorption

theorem unital_main
    (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (hsimple : Pureness.TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hnuc : Pureness.IsNuclear.{0,0} A) (hcmp : DirectComparison.StrictComparison A) :
    Nonempty (UnitalSpatialEquiv A) ∧
    ∀ (htr : Nonempty (TracialState A)),
      letI := htr
      ∀ (U : Ultrafilter ℕ), (U : Filter ℕ)≤atTop → DirectComparison.UniformGamma A U := by
  classical
  constructor
  · apply unitalSpatialEquiv_of_nonempty
    let U : Ultrafilter ℕ := Ultrafilter.of atTop
    have hfree : (U : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
    by_cases h : Nonempty (TracialState A)
    · let := h
      exact DirectComparison.comparison_original_jiang_su_absorption (A := A) U hfree
        hnuc hsimple hinf hcmp
    · let : IsEmpty (TracialState A) := ⟨fun τ => h ⟨τ⟩⟩
      exact CurrentMain.Traceless.empty_comparison_original_jiang_su_absorption (A := A) U hfree
        hnuc hsimple hinf (DirectComparison.StrictComparison.empty_trace hcmp)
  · intro htr
    let := htr
    intro U hfree
    exact DirectComparison.comparison_uniform_gamma U hfree hsimple hinf hcmp hnuc

private theorem nonunitalSpatialEquiv_of_nonempty
    (A D : Type) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D]
    (absorption : Nonempty (A ≃⋆ₐ[ℂ] ActualSpatial.NonunitalTensor A D)) :
    Nonempty (NonunitalSpatialEquivCore A D) := by
  exact absorption

theorem stably_projectionless_main
    (A : Type) [algebra : NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    [Nonempty (NonunitalGamma.NormalizedTrace A)]
    [CompactSpace (NonunitalGamma.NormalizedTrace A)]
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : NonunitalGamma.StablyProjectionless A)
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A)
    (hcone : NonunitalGamma.AllDenselyFiniteTracesBounded A)
    (hcmp : NonunitalGamma.StrictComparison hcone) :
    (∀ (U : Ultrafilter ℕ), (U : Filter ℕ)≤atTop → NonunitalGamma.UniformGamma A U) ∧
    Nonempty (@NonunitalSpatialEquivCore A OriginalJiangSu.Algebra algebra
        (@SequentialCStar.System.instCStarAlgebraSubtypeFamilyQuotientMemStarSubalgebraComplexLimit.{0}
          OriginalJiangSu.Stage
          (fun index : ℕ =>
            JiangSuConstruction.instCStarAlgebraSubtypeContinuousMapElemRealIntervalTensorMatMemStarSubalgebraComplexDimensionDrop
              (OriginalJiangSu.pair index).p (OriginalJiangSu.pair index).q)
          OriginalJiangSu.stageNontrivial OriginalJiangSu.system)
      OriginalJiangSu.algebraOrder OriginalJiangSu.algebraStarOrder) := by
  refine ⟨fun U hfree => NonunitalGamma.stably_projectionless_uniform_gamma U hfree
    hsimple hstable hcone hcmp hnuc, ?_⟩
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  let : Fact ((U : Filter ℕ)≤atTop) := ⟨Ultrafilter.of_le atTop⟩
  exact @nonunitalSpatialEquiv_of_nonempty A OriginalJiangSu.Algebra algebra
    (@SequentialCStar.System.instCStarAlgebraSubtypeFamilyQuotientMemStarSubalgebraComplexLimit.{0}
      OriginalJiangSu.Stage
      (fun index : ℕ =>
        JiangSuConstruction.instCStarAlgebraSubtypeContinuousMapElemRealIntervalTensorMatMemStarSubalgebraComplexDimensionDrop
          (OriginalJiangSu.pair index).p (OriginalJiangSu.pair index).q)
      OriginalJiangSu.stageNontrivial OriginalJiangSu.system)
    OriginalJiangSu.algebraOrder OriginalJiangSu.algebraStarOrder
    (NonunitalSI.comparison_original_jiang_su_absorption (A := A) U
      hnuc hsimple hstable hcone hcmp)

end OriginalJiangSu.Main

end

end OAI
