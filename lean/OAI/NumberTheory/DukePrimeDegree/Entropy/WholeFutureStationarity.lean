import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixNullAmbient
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCountableAtlas
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureCountableCover

namespace OAI

/-! # Global stationarity of the actual whole-future kernel

The countable family of genuine quotient boxes covers each bounded
future fiber. Local mass-containment events therefore cover almost every
point, and their stationary restrictions glue to the ambient measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]

theorem wholeFutureKernel_stationary
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
          (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂μ, κ x =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    μ.bind κ = μ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree := ae_upperRoot_stabilizer_trivial d μ hA
  obtain ⟨S,hS,hcover⟩ := C.exists_countable_translates_cover c hP hf z₀
  let : Countable S := hS.to_subtype
  let (g : S) (j : ℕ) : Countable
      {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j} :=
    (C.longBoxFamily_countable c hP hf g.val 1 j).to_subtype
  let I := Σ g : S, Σ j : ℕ,
    {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j}
  let B (i : I) := i.2.2.val
  let F (i : I) := C.timeParam c hP hf i.1.val
  have hBR (i : I) : (B i).time ⊆ c.remainingWindow (1+i.2.1) 0 := by
    rw [C.longBoxFamily_time c hP hf i.1.val 1 i.2.1 (B i) i.2.2.prop]
    simp only [EliminationChain.remainingWindow, Nat.cast_zero, add_zero, subset_refl]
  let K (i : I) := (B i).regularLeafKernel (1+i.2.1) (hBR i) μ hfree
  let E (i : I) := {z | K i z.1 (countableFutureFiber T Q (F i) z \ (B i).time) = 0}
  let A (i : I) := F i '' (E i ∩ (B i).domain)
  have hE (i : I) : MeasurableSet (E i) := by
    have hF : Measurable (F i) :=
      (C.timeParam_localHomeomorph c hP hf i.1.val).continuous.measurable
    have he := measurableSet_future_mass_contained (K i) hT hQ hF (B i).time
      (B i).time_open.measurableSet
    have hle : (⨆ m, transverseLabelSigma
        (fun z => countableFutureCode T Q m (F i z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact hle (E i) he
  apply stationary_of_countable_indexed_restrictions κ μ A
  · intro i
    exact (B i).measurableSet_param_image _
      ((hE i).inter ((B i).transverse_open.prod (B i).time_open).measurableSet)
      inter_subset_right
  · filter_upwards [hfree,hbound] with x hx hb
    have hc : x ∈ ⋃ g ∈ S, range (C.timeParam c hP hf g) := by rw [hcover]; trivial
    obtain ⟨g,hg,z,hz⟩ := by simpa only [mem_iUnion,mem_range] using hc
    have hi := C.timeParam_injective_of_free_at_coordinate c hP hf g z (by simpa [hz] using hx)
    obtain ⟨R,hR⟩ := hb
    obtain ⟨B',hB',hs,ht,j,hj,hfuture⟩ :=
      C.exists_countable_box_containing_futureFiber c hP hf g z.1 z.2 hi T Q 1 R
        (by simpa [T,hz] using hR)
    obtain ⟨j',hj'⟩ := mem_iUnion.mp hB'
    let i : I := ⟨⟨g,hg⟩,j',⟨B',hj'⟩⟩
    apply mem_iUnion.mpr ⟨i,?_⟩
    refine ⟨z,⟨?_,hs,ht⟩,hz⟩
    change K i z.1 (countableFutureFiber T Q (C.timeParam c hP hf g) z \ B'.time) = 0
    have hsub : countableFutureFiber T Q (C.timeParam c hP hf g) z ⊆ B'.time := hfuture
    rw [sdiff_eq_empty.mpr hsub,measure_empty]
  · intro i
    exact (B i).stationary_image_massContained (1+i.2.1) (hBR i) μ hfree ell hell Q hQ
      hgood κ hκ

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
