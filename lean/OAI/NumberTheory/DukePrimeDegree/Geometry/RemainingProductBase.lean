import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBasedMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductMass

namespace OAI

/-! # The completed-prefix base case of the leaf-product induction -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n (allPositiveRoots n) T} {g : G n}

theorem ae_completed_basedLeaf_eq_intrinsicProduct
    (c : EliminationChain (allPositiveRoots n) D) (hdone : c = .done)
    (hP : InitialRootPattern (allPositiveRoots n))
    (hfinal : c.finalEntries = allPositiveRoots n)
    (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      c.remainingGroupLeafMeasure hP hfinal (A.basedLeaf R μ z) =
        c.remainingIntrinsicProduct hP hfinal μ (Pfx.timeParam c hP hfinal g z) := by
  subst c
  filter_upwards [A.ae_basedLeaf_spec R hAR μ hfree] with z hz
  rw [EliminationChain.remainingIntrinsicProduct_done]
  have hm : A.basedLeaf R μ z univ = 1 := by
    simpa only [EliminationChain.cube] using hz.2
  have he : ⇑(EliminationChain.done.remainingWordHomeomorph hP hfinal) =
      fun _ => (1 : positiveRootGeneratedGroup (allPositiveRoots n \ allPositiveRoots n)) := by
    funext t
    apply Subtype.ext
    rfl
  rw [EliminationChain.remainingGroupLeafMeasure,he,Measure.map_const,hm,one_smul]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
