import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixSelfConditional
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCountableAtlas
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureCountableCover

namespace OAI

/-! # Self-consistency of the global root-future kernel

Local self-consistency on a countable atlas passes to the actual ambient
kernel. Together with stationarity this identifies its conditional law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSingletonClass V]

theorem wholeFutureKernel_self_constant
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
    ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
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
  have hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, A i := by
    filter_upwards [hfree,hbound] with x hx hb
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
  have H : ∀ᵐ x ∂μ.restrict (⋃ i, A i), ∀ᵐ y ∂κ x, κ y=κ x := by
    apply (ae_restrict_iUnion_iff A _).mpr
    intro i
    exact (B i).selfConstant_image_massContained (1+i.2.1) (hBR i) μ hfree ell hell Q hQ
      hgood κ hκ
  rwa [Measure.restrict_eq_self_of_ae_mem hcover] at H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
