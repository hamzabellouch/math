import OAI.NumberTheory.DukePrimeDegree.Entropy.AuxiliaryKernelEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.GlobalFutureKernelConstancy
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPredecessorInformation

namespace OAI

/-! # Actual root information bounds from auxiliary recurrent fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

/-- Once the recurrent auxiliary observation removes the transverse
coordinates, its only entropy cost is its countable Shannon sum. All
kernel terms here are the intrinsic root-future measures. -/
theorem predecessor_entropyRate_le_root_information_add_auxiliary
    {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
        (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    {M : ℕ} (B : X (d+1) → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y →
      Q (rightAction x (diagonalOneParameter ell hell (-1)))=
        Q (rightAction y (diagonalOneParameter ell hell (-1))) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ)
    (hdecode : ∀ x, decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x)
    (R : X (d+1) → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (E : Set (X (d+1))) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hrelative : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      (∀ k : ℕ, R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : c.Time, rightAction x (c.word u)=y)
    (L : ℕ) :
    observationEntropyRate μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
      (heightClip Q L) ≤
      (∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨F,hF,hconst⟩ := C.exists_conull_leafFutureKernel_constancy c hP hf z₀
    μ ell hell Q hbound κ hversion
  have hEF : ∀ᵐ x ∂μ, x ∈ F ∩ E := hF.and hE
  have hk : ∀ x ∈ F ∩ E, ∀ y ∈ F ∩ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y := by
    intro x hx y hy hq hr
    exact hconst x hx.1 y hy.1 (hrelative x hx.2 y hy.2 hq hr) hq
  have H := predecessor_auxiliary_kernel_entropyRate_le μ hT Q hQ B hB href
    decode hdecode R hR hfinite κ (F ∩ E) hEF hk L
  have HI := c.predecessor_root_information d hP hf μ hA ell hell Q hQ κ
    hstat hself hversion hmass B hB href decode hdecode
  rw [HI] at H
  exact H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
