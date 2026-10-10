import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralPatchCover

namespace OAI

/-! # Actual atomic roots give full-measure graphs in every small neutral patch -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem SmallNeutralPatch.exists_atomic_graph {d : ℕ} {ε : ℝ}
    (P : SmallNeutralPatch (d+1) ε)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ x ∂μ, x ∈ P.raw → x ∈ neutralQuotientParam (d+1) P.center ''
        ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F)) := by
  let τ := firstCoordinateSlice ((quotientLiftMeasure (d+1) μ s).comap
    (fun z => P.center*neutralProductParam (d+1) z)) K₀
  let := neutralCoordinateBase_locallyCompact (d+1)
  let := neutralCoordinateBase_secondCountable (d+1)
  let : IsFiniteMeasureOnCompacts τ :=
    translated_neutral_transverse_finiteOnCompacts (d+1) P.center μ s hsm hs K₀ hK₀
  obtain ⟨F,hF,_,hunique,hfull⟩ := actual_neutral_patch_graph_of_atomic_roots
    d P.center P.box P.bound P.time_bound μ s hsm hs hA η K₀ hK₀ hηK₀
    P.base P.neutral (P.neutral_open.measure_pos η P.neutral_nonempty).ne'
    P.in_box hatom
  refine ⟨F,hF,hunique,?_⟩
  exact neutral_patch_image_ae_graph (d+1) P.center μ s hsm hs τ η
    (translated_neutral_product (d+1) P.center μ s hsm hs hA η K₀ hK₀ hηK₀)
    P.base P.base_open.measurableSet P.neutral P.neutral_open.measurableSet
    (neutralQuotientParam_injOn (d+1) P.center P.box _ P.in_box) F hF hfull

end DukePrimeDegree

end

end OAI
