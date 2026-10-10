import OAI.NumberTheory.DukePrimeDegree.Entropy.SubordinateFutureBoxes
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureShift

namespace OAI

/-! # Bounded boxes for the future excluding the present

A single time shift carries a bounded full-future fiber into a compact
inverse diagonal image. Thus one finite cube contains all future fibers
almost everywhere. Their actual coordinate representatives fit inside
bounded quotient boxes at almost every sample.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

theorem ae_remainingFutureAtom_one_bounded (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D)
    (μ : Measure (X (d+1)))
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hT : MeasurePreserving
      (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (hbound : ∀ᵐ x ∂μ, c.remainingFutureAtom ell hell Q 0 x ⊆ c.cube 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ᵐ x ∂μ, c.remainingFutureAtom ell hell Q 1 x ⊆ c.cube R := by
  let E := c.rootDilation ell 1
  let K := E.symm '' c.closedCube 1
  have hK : IsCompact K := (c.closedCube_compact 1).image E.symm.continuous
  obtain ⟨m,hm⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ K)
    (c.remainingWindow_mono 1).directed_le
  refine ⟨1+m,by positivity,?_⟩
  filter_upwards [hT.quasiMeasurePreserving.ae hbound] with x hx u hu
  have hu' : E u ∈ c.remainingFutureAtom ell hell Q 0
      (rightAction x (diagonalOneParameter ell hell (-1))) := by
    have hp : u ∈ (c.rootDilation ell 1) ⁻¹'
        c.remainingFutureAtom ell hell Q 0
          (rightAction x (diagonalOneParameter ell hell (-1))) := by
      rw [c.remainingFutureAtom_shift]
      exact hu
    exact hp
  apply hm
  exact ⟨E u,c.cube_subset_closedCube 1 (hx hu'),E.symm_apply_apply u⟩

end EliminationChain
namespace RootPrefixBox

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates n P V} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_exists_bounded_wholeFuture_box
    (B : RootPrefixBox C c hP hf g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ᵐ x ∂μ, ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word v)))=Q (T^[k+m] x)) →
        v ∈ c.cube R) :
    ∀ᵐ z ∂B.coordinateMeasure μ,
      ∃ (B' : RootPrefixBox C c hP hf g) (S : ℝ), 0 < S ∧
        z.1 ∈ B'.transverse ∧ z.2 ∈ B'.time ∧ B'.time ⊆ c.cube S ∧
        {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (z.1,u))) =
          Q (T^[k+m] (C.timeParam c hP hf g z))} ⊆ B'.time := by
  have hinj := B.ae_injective_slice_of_ae_free μ hfree
  have hi : ∀ᵐ z ∂B.coordinateMeasure μ,
      Function.Injective (fun t => C.timeParam c hP hf g (z.1,t)) :=
    ae_of_ae_map measurable_fst.aemeasurable hinj
  filter_upwards [hi,B.ae_coordinate_of_ambient μ hbound] with z hz hb
  exact C.exists_bounded_box_containing_futureFiber c hP hf g z.1 z.2 hz T Q m R hb

end RootPrefixBox
end DukePrimeDegree

end

end OAI
