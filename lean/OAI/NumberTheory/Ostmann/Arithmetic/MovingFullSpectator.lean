import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSpectator

namespace OAI

/-! # A fixed rational spectator diagram for the full original coefficient -/

namespace Ostmann
open scoped Classical

/-- The diagram is fixed before the bulk values and giants are supplied.
Its equality with the full coefficient is proved from the recursive weight,
including every original cutoff and the compensation divisibility tests. -/
theorem moving_full_coefficient_spectator_diagram {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod q) ≠ 0)
    (n : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n (movingSlotValues value n small) : ℕ) : ZMod q) ≠ 0)
    (hsamples : (samples.values value).UnitsAt q) :
    ∃ (C : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n C),
      ∀ (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (bulk : TreeLeafTuple (List σ) n)
        (bulkResidue : TreeLeafTuple (ZMod q)ˣ n) (XL XR : ℕ) (A B : (ZMod q)ˣ),
        (XL : ZMod q) = A → (XR : ZMod q) = B →
        TreeNaturalLift n (movingSlotValues value n bulk) bulkResidue →
        let state : MovingSlotState σ := ⟨n, buildMovingSlotData n t small bulk samples, XL, XR⟩
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
          (movingSlotCutoff value childBound pivotBound extra) n state t =
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
          (movingSlotCutoff value childBound pivotBound extra) n state t *
          rationalTreeAmplitude g D R A B (transferConjugations n false) bulkResidue := by
  let T := buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)
  have hT : T.UnitsAt q := buildMovingGiantTree_units t _ _ hfreq hsmall hsamples
  obtain ⟨C, R, _, _, hR⟩ := T.exists_residue_diagram hT
  refine ⟨C, R, ?_⟩
  intro g D bulk bulkResidue XL XR A B hA hB hbulk
  dsimp only
  let state : MovingSlotState σ := ⟨n, buildMovingSlotData n t small bulk samples, XL, XR⟩
  let W := recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
    (movingSlotCutoff value childBound pivotBound extra) n state t
  rw [movingSlotWeight_spectator value childBound pivotBound F extra hextra g D _ t
    (buildMovingSlotData_follows n t small bulk samples) XL XR,
    buildMovingSlotData_spectator]
  by_cases hW : W = 0
  · change W * _ = W * _
    rw [hW, zero_mul, zero_mul]
  · have hi := movingSlotWeight_nonzero_integral value childBound pivotBound F extra
      (buildMovingSlotData n t small bulk samples) t (buildMovingSlotData_follows n t small bulk samples)
      XL XR hW
    have hi' := (buildMovingSlotData_integral value n t small bulk samples XL XR).mp hi
    have he := hR g D XL XR A B (movingSlotValues value n bulk) bulkResidue hA hB hbulk hi' false
    change W * _ = W * _
    exact congrArg (fun z : ℂ => W * z) he

end Ostmann

end OAI
