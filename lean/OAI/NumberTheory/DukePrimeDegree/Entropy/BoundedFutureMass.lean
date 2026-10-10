import OAI.NumberTheory.DukePrimeDegree.Entropy.BoundedFutureObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureInformation

namespace OAI

/-! # Positive finite mass of entire subordinate future atoms -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The entire future atom has positive finite intrinsic mass. No
intersection with an auxiliary bounded leaf box is needed. -/
theorem exists_low_entropy_positive_future_mass (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      ∀ᵐ x ∂μ,
        0 < (completeRootChain (d+1)).remainingTimeProduct
          (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x
          ((completeRootChain (d+1)).remainingFutureAtom ell hell Q 0 x) ∧
        (completeRootChain (d+1)).remainingTimeProduct
          (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x
          ((completeRootChain (d+1)).remainingFutureAtom ell hell Q 0 x) ≤ 1 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨H,Q,hH,hQ,hcompact,hfinite,hent,_,hbound,hgood⟩ :=
    exists_bounded_low_entropy_subordinate_observation d ell hell hgap μ hA hε
  let c := completeRootChain (d+1)
  have hP : InitialRootPattern (∅ : Finset (Fin (d+1) × Fin (d+1))) := by
    intro p hp
    simp at hp
  refine ⟨H,Q,hH,hQ,hcompact,hfinite,hent,?_⟩
  filter_upwards [hbound,hgood,
    EliminationChain.ae_remainingTimeProduct_nhds_pos d c hP (completeRootChain_final _) μ hA,
    EliminationChain.ae_remainingTimeProduct_unit d c hP (completeRootChain_final _) μ]
    with x hx hg hp hu
  have hN : c.remainingFutureAtom ell hell Q 0 x ∈ 𝓝 c.zeroTime := by
    change ∀ᶠ s in 𝓝 c.zeroTime, _
    filter_upwards [hg] with s hs
    intro k
    simpa only [Nat.add_zero] using hs k
  have hsub : c.remainingFutureAtom ell hell Q 0 x ⊆ c.cube 1 := by
    intro s hs
    exact hx s (by simpa only [c, EliminationChain.remainingFutureAtom, Nat.add_zero, Set.mem_ofPred_eq] using hs)
  exact ⟨hp _ hN, (measure_mono hsub).trans_eq hu⟩

/-- The subordinate observation can be chosen with arbitrarily small
height entropy and an integrable whole-future information function.
Its canonical mean is proved, rather than assumed as leaf data. -/
theorem exists_low_entropy_integrable_future_information (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      let c := completeRootChain (d+1)
      let ν := c.remainingTimeProduct
        (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ
      let I := fun x => -Real.log
        (ν x (c.remainingFutureAtom ell hell Q 0 x) /
          ν x (c.remainingFutureAtom ell hell Q 1 x)).toReal
      Integrable I μ ∧ (∫ x, I x ∂μ) =
        ∑ p : allPositiveRoots (d+1),
          (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  obtain ⟨H,Q,hH,hQ,hcompact,hfinite,hent,hmass⟩ :=
    exists_low_entropy_positive_future_mass d ell hell hgap μ hε
  refine ⟨H,Q,hH,hQ,hcompact,hfinite,hent,?_⟩
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have HH := EliminationChain.remainingFutureInformation_integrable_integral d
    (completeRootChain (d+1)) (by intro p hp; simp at hp)
    (completeRootChain_final (d+1)) μ hA ell hell Q hQ hmass
  refine ⟨HH.1, HH.2.trans ?_⟩
  let f : Fin (d+1) × Fin (d+1) → ℝ := fun p =>
    (ell p.2-ell p.1) * canonicalRootCoefficient d μ p.1 p.2
  change (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) =
    ∑ p : ↥(allPositiveRoots (d+1)), f p
  rw [← Finset.sum_subtype (allPositiveRoots (d+1) \ ∅) (by intro p; rfl) f,
    ← Finset.sum_subtype (allPositiveRoots (d+1)) (by intro p; rfl) f,
    Finset.sdiff_empty]

end DukePrimeDegree

end

end OAI
