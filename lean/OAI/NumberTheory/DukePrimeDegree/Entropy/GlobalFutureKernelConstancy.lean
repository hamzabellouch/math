import OAI.NumberTheory.DukePrimeDegree.Entropy.LocalFutureKernelConstancy
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureCountableCover
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCountableAtlas

namespace OAI

/-! # The actual future kernel is constant on conull leaf-future fibers

A fixed countable atlas of long root boxes lets the pointwise local
statement hold on one ambient conull set. Any bounded root-future fiber
fits into one of these boxes, so two good points on the same root orbit
with the same future names have identical ambient kernels.
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

theorem exists_conull_leafFutureKernel_constancy
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
        (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E, (∃ u : c.Time, rightAction x (c.word u)=y) →
        (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) → κ x=κ y := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
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
  have hBR (i : I) : (B i).time ⊆ c.remainingWindow (1+i.2.1) 0 := by
    rw [C.longBoxFamily_time c hP hf i.1.val 1 i.2.1 (B i) i.2.2.prop]
    simp only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero,subset_refl]
  choose E hE hconst using fun i : I =>
    (B i).exists_conull_futureKernel_chart_constancy (1+i.2.1) (hBR i)
      μ hfree ell hell Q κ hκ
  let A := {x | (∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1) ∧
    (∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+1] (rightAction x (c.word v)))=Q (T^[k+1] x)) →
        v ∈ c.cube R) ∧ ∀ i : I, x ∈ E i}
  have hAgood : ∀ᵐ x ∂μ, x ∈ A := by
    filter_upwards [hfree,hbound,ae_all_iff.mpr hE] with x hx hb he
    exact ⟨hx,hb,he⟩
  refine ⟨A,hAgood,?_⟩
  intro x hx y hy hrel hname
  obtain ⟨u,hu⟩ := hrel
  have hxc : x ∈ ⋃ g ∈ S, range (C.timeParam c hP hf g) := by rw [hcover]; trivial
  obtain ⟨g,hg,z,hz⟩ := by simpa only [mem_iUnion,mem_range] using hxc
  have hi := C.timeParam_injective_of_free_at_coordinate c hP hf g z
    (by simpa only [hz] using hx.1)
  obtain ⟨R,hR⟩ := hx.2.1
  obtain ⟨B',hB',hs,ht,j,hj,hfuture⟩ := C.exists_countable_box_containing_futureFiber
    c hP hf g z.1 z.2 hi T Q 1 R (by simpa only [hz] using hR)
  obtain ⟨j',hj'⟩ := mem_iUnion.mp hB'
  let i : I := ⟨⟨g,hg⟩,j',⟨B',hj'⟩⟩
  let w : (UpperRootTransverse (d+1) × V) × c.Time :=
    (z.1,(c.remainingRebase hP hf z.2).symm u)
  have hw : C.timeParam c hP hf g w=y := by
    dsimp only [w]
    rw [C.timeParam_rebased c hP hf g z.1 z.2,
      (c.remainingRebase hP hf z.2).apply_symm_apply,hz,hu]
  have hwt : w.2 ∈ B'.time := by
    apply hfuture
    intro k
    change Q (T^[k+1] (C.timeParam c hP hf g w))=
      Q (T^[k+1] (C.timeParam c hP hf g z))
    rw [hw,hz]
    exact hname k
  have H := hconst i z ⟨hs,ht⟩ w ⟨hs,hwt⟩
    (by simpa only [i,B,hz] using hx.2.2 i)
    (by simpa only [i,B,hw] using hy.2.2 i) rfl
    (fun k => by simpa only [i,B,hz,hw] using (hname k).symm)
  simpa only [i,B,hz,hw] using H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
