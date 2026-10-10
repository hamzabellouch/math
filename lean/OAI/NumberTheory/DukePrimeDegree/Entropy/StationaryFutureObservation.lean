import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureStationarity
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureSelfConditional
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureProbabilityKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureShiftBounds
import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralSubordinateObservation

namespace OAI

/-! # A stationary whole-future kernel for the low-entropy observation -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_low_entropy_stationary_wholeFutureKernel (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H Q : X (d+1) → ℕ) (κ : Kernel (X (d+1)) (X (d+1))),
      Measurable H ∧ Measurable Q ∧ IsMarkovKernel κ ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
      μ.bind κ = μ ∧
      (∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x) ∧
      (∀ᵐ x ∂μ,
        let c := completeRootChain (d+1)
        κ x = ((anchorNormalize (c.remainingTimeProduct
          (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x)
          (c.remainingFutureAtom ell hell Q 1 x)).restrict
          (c.remainingFutureAtom ell hell Q 1 x)).map
          (fun u => rightAction x (c.word u))) ∧
      (∀ᵐ x ∂μ,
        let c := completeRootChain (d+1)
        0 < c.remainingTimeProduct (by intro p hp; simp at hp)
          (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
        c.remainingTimeProduct (by intro p hp; simp at hp)
          (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) ∧
      (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
      (∀ x y, Q y=Q x → H y=H x) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧
          ∀ i j, ell j < ell i → g.val i j = 0) := by
  let c := completeRootChain (d+1)
  have hP : InitialRootPattern (∅ : Finset (Fin (d+1) × Fin (d+1))) := by
    intro p hp
    simp at hp
  have hf := completeRootChain_final (d+1)
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨H,Q,hH,hQ,hcompact,hfinite,hent,hweak,hbound,hgood,hstep,hrefine,hneutral⟩ :=
    exists_bounded_neutral_subordinate_observation d ell hell hgap μ hA hε
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
  have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
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
  exact ⟨H,Q,κ,hH,hQ,inferInstance,hcompact,hfinite,hent,hneutral,hs,hself,hk,hmass,hstep,hrefine,hweak⟩

end DukePrimeDegree

end

end OAI
