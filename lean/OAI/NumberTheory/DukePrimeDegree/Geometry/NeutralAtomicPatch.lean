import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralPrefixMap
import OAI.NumberTheory.DukePrimeDegree.Geometry.IndependentGraphSlice
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingAtomicProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.TranslatedNeutralProduct

namespace OAI

/-! # Atomic root kernels give a neutral-independent support graph in each patch -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_patch_graph_of_atomic_kernel (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (τ : Measure (NeutralCoordinateBase n)) [SFinite τ]
    (η : Measure (transverseNeutralSpace n)) [SFinite η]
    (hprod : (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=τ.prod η)
    (A : Set (NeutralCoordinateBase n))
    (K : Set (transverseNeutralSpace n)) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix n z ∈ B.domain)
    (hatom : ∀ᵐ z ∂B.coordinateMeasure μ, B.conditionalKernel μ z.1=Measure.dirac z.2) :
    ∃ F : Set (NeutralCoordinateBase n), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) := by
  let : NeZero (η.restrict K) := ⟨by
    intro he
    have H := congrArg (fun m : Measure (transverseNeutralSpace n) => m univ) he
    simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at H
    exact hηK H⟩
  have hle := neutralToPrefix_restrict_le n g B μ s hsm hs (A ×ˢ K) hAB
  rw [hprod,←Measure.prod_restrict] at hle
  apply independent_graph_of_fiber_map (τ.restrict A) (η.restrict K)
    (B.coordinateMeasure μ) (B.conditionalKernel μ) hatom (neutralToPrefix n)
    (neutralToPrefix_isOpenEmbedding n).continuous.measurable
    (Measure.absolutelyContinuous_of_le hle)
  · exact neutralToPrefix_base n
  · intro x y _ hv hu
    exact neutralToPrefix_fiber_injective n x y hv hu

theorem neutral_patch_graph_of_atomic_roots (d : ℕ) (g : G (d+1))
    (B : RootPrefixBox (neutralEmptyPrefix (d+1)) (completeRootChain (d+1))
      (emptyRootPattern (d+1)) (completeRootChain_final (d+1)) g)
    (R : ℝ) (hBR : B.time ⊆ (completeRootChain (d+1)).remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (τ : Measure (NeutralCoordinateBase (d+1))) [SFinite τ]
    (η : Measure (transverseNeutralSpace (d+1))) [SFinite η]
    (hprod : (quotientLiftMeasure (d+1) μ s).comap
      (fun z => g*neutralProductParam (d+1) z)=τ.prod η)
    (A : Set (NeutralCoordinateBase (d+1)))
    (K : Set (transverseNeutralSpace (d+1))) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix (d+1) z ∈ B.domain)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) :=
  neutral_patch_graph_of_atomic_kernel (d+1) g B μ s hsm hs τ η hprod A K hηK hAB
    (B.ae_conditionalKernel_eq_dirac_of_atomic_roots R hBR μ hatom)

theorem actual_neutral_patch_graph_of_atomic_roots (d : ℕ) (g : G (d+1))
    (B : RootPrefixBox (neutralEmptyPrefix (d+1)) (completeRootChain (d+1))
      (emptyRootPattern (d+1)) (completeRootChain_final (d+1)) g)
    (R : ℝ) (hBR : B.time ⊆ (completeRootChain (d+1)).remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (A : Set (NeutralCoordinateBase (d+1)))
    (K : Set (transverseNeutralSpace (d+1))) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix (d+1) z ∈ B.domain)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    let τ := firstCoordinateSlice
      ((quotientLiftMeasure (d+1) μ s).comap (fun z => g*neutralProductParam (d+1) z)) K₀
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) := by
  let := neutralCoordinateBase_locallyCompact (d+1)
  let := neutralCoordinateBase_secondCountable (d+1)
  let := translated_neutral_transverse_finiteOnCompacts (d+1) g μ s hsm hs K₀ hK₀
  exact neutral_patch_graph_of_atomic_roots d g B R hBR μ s hsm hs _ η
    (translated_neutral_product (d+1) g μ s hsm hs hA η K₀ hK₀ hηK₀)
    A K hηK hAB hatom

end DukePrimeDegree

end

end OAI
