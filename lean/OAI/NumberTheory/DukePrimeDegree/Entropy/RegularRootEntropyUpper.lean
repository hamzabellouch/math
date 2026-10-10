import OAI.NumberTheory.DukePrimeDegree.Entropy.AuxiliaryRootInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.StationaryCoverObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralFiniteCodes
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorSymbols

namespace OAI

/-! # Entropy upper bounds from small auxiliary root-orbit observations

The intrinsic stationary future kernel is built for the given bounded
branching observation.  An auxiliary observation only removes transverse
coordinates from joint future fibers; it need not generate the ambient
measurable space.  Its sole entropy cost is its countable Shannon sum.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Each finite clip of a bounded branching observation is controlled by
actual root information and the Shannon sum of the auxiliary observation.
The stationary kernel and finite predecessor symbols are constructed in
this proof, rather than supplied as additional hypotheses. -/
theorem heightClip_entropyRate_le_root_sum_add_auxiliary (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∀ v : UpperRootTime (d+1),
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word v))) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      v ∈ (completeRootChain (d+1)).cube 1)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))
    (hfinite : UniformFinitePredecessors
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q)
    (R : X (d+1) → ℕ) (hR : Measurable R)
    (hShannon : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (E : Set (X (d+1))) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hrelative : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      (∀ k : ℕ,
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : UpperRootTime (d+1), rightAction x ((completeRootChain (d+1)).word u)=y)
    (L : ℕ) :
    observationEntropyRate μ (fun z => rightAction z (diagonalOneParameter ell hell (-1)))
      (heightClip Q L) ≤
      (∑ p : allPositiveRoots (d+1),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  let c := completeRootChain (d+1)
  have hP : InitialRootPattern (∅ : Finset (Fin (d+1) × Fin (d+1))) := by
    intro p hp
    simp at hp
  have hf := completeRootChain_final (d+1)
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hb : ∀ᵐ x ∂μ, c.remainingFutureAtom ell hell Q 0 x ⊆ c.cube 1 := by
    filter_upwards [hbound] with x hx v hv
    exact hx v (by simpa only [c,EliminationChain.remainingFutureAtom,Nat.add_zero,
      Set.mem_ofPred_eq] using hv)
  have hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1 := by
    filter_upwards [hb,hgood,c.ae_remainingTimeProduct_nhds_pos d hP hf μ hA,
      c.ae_remainingTimeProduct_unit d hP hf μ] with x hx hg hp hu
    have hN : c.remainingFutureAtom ell hell Q 0 x ∈ 𝓝 c.zeroTime := by
      change ∀ᶠ v in 𝓝 c.zeroTime, _
      filter_upwards [hg] with v hv k
      simpa only [Nat.add_zero] using hv k
    exact ⟨hp _ hN,(measure_mono hx).trans_eq hu⟩
  have hb1 := c.ae_bounded_one_future_of_zero d μ ell hell Q hT hb
  have hm1 := c.ae_one_future_mass_pos_ne_top d hP hf μ hA ell hell Q hQ hmass
  obtain ⟨η,hη,hversion⟩ := c.exists_wholeFutureProbabilityKernel d hP hf μ hA
    ell hell Q hQ 1 hm1
  let := hη
  let κ := c.futureAmbientKernel hf η
  have hk : ∀ᵐ x ∂μ, κ x =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u)) := by
    filter_upwards [hversion] with x hx
    change (η x).map _ = _
    rw [hx]
  have hs : μ.bind κ = μ :=
    (RootPrefixCoordinates.empty (d+1)).wholeFutureKernel_stationary c hP hf
      ((upperRootIdentity (d+1),PUnit.unit),c.zeroTime) μ ell hell Q hQ hgood hb1 κ hk
  have hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x :=
    (RootPrefixCoordinates.empty (d+1)).wholeFutureKernel_self_constant c hP hf
      ((upperRootIdentity (d+1),PUnit.unit),c.zeroTime) μ ell hell Q hQ hgood hb1 κ hk
  obtain ⟨M,B,decode,hB,href,hdecode⟩ :=
    exists_finite_predecessor_observation T hT.measurable Q hQ hfinite
  have H := (RootPrefixCoordinates.empty (d+1)).predecessor_entropyRate_le_root_information_add_auxiliary
    c hP hf ((upperRootIdentity (d+1),PUnit.unit),c.zeroTime) μ ell hell Q hQ hb1
      κ hs hself hk hmass B hB href decode hdecode R hR hShannon E hE hrelative L
  let f : Fin (d+1) × Fin (d+1) → ℝ := fun p =>
    (ell p.2-ell p.1)*canonicalRootCoefficient d μ p.1 p.2
  have hsum : (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) =
      ∑ p : allPositiveRoots (d+1), f p := by
    rw [← Finset.sum_subtype (allPositiveRoots (d+1) \ ∅) (by intro p; rfl) f,
      ← Finset.sum_subtype (allPositiveRoots (d+1)) (by intro p; rfl) f,
      Finset.sdiff_empty]
  change observationEntropyRate μ T (heightClip Q L) ≤
    (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) + _ at H
  rw [hsum] at H
  exact H

/-- Arbitrarily small auxiliary Shannon costs remove the transverse term.
The bilateral neutral-fiber property belongs to Q itself; no generating
property of the auxiliary observations is needed. -/
theorem negative_diagonal_entropy_le_root_sum_of_small_auxiliary (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∀ v : UpperRootTime (d+1),
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word v))) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      v ∈ (completeRootChain (d+1)).cube 1)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))
    (hfinite : UniformFinitePredecessors
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q)
    (hneutral : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (haux : ∀ ε : ℝ, 0 < ε →
      ∃ R : X (d+1) → ℕ, Measurable R ∧
        Summable (fun n => Real.negMulLog (μ.real {x | R x=n})) ∧
        (∑' n, Real.negMulLog (μ.real {x | R x=n})) < ε ∧
        ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
          ∀ x ∈ E, ∀ y ∈ E,
            (∀ k : ℕ,
              Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
              Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
            (∀ k : ℕ,
              R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
              R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
            ∃ u : UpperRootTime (d+1),
              rightAction x ((completeRootChain (d+1)).word u)=y) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  apply measureEntropy_le_of_bilateral_heightClip_bounds d ell hell Q hQ μ hA hneutral
  intro L
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,hShannon,hsmall,E,hE,hrelative⟩ := haux ε hε
  exact (heightClip_entropyRate_le_root_sum_add_auxiliary d ell hell μ Q hQ
    hbound hgood hfinite R hR hShannon E hE hrelative L).trans
      (by linarith [hsmall.le])

end DukePrimeDegree

end

end OAI
