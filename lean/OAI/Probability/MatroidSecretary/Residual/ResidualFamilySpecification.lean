import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet

open Set Finset Pivots MainAlgorithm

/-- Source `lem:pattern-family`, with its fixed-before-focal-bits quantifiers.
The source uses κ=2^100; this statement also covers every κ≥2. -/
def PatternFamilyClaim : Prop :=
  ∀ {n : ℕ}
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ) (_hκ : 2 ≤ κ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (_hsize : κ ≤ (trueGroup M d s i).card) (ε : Fin 2),
    ∃ family : Finset (Finset (Fin n)),
      (∀ R ∈ family, R ⊆ trueGroup M d s i) ∧
      (family.card : ℝ) ≤ Real.exp
        (1000 * Real.log (κ : ℝ) / (κ : ℝ) * (trueGroup M d s i).card) ∧
      ∀ (A B C : Finset (Fin n)),
        A ⊆ trueGroup M d s i → B ⊆ trueGroup M d s i →
        C ⊆ trueGroup M d s i → A.Nonempty →
        let U := trueGroup M d s i
        let f := focalMasks d U A B C
        let h := focalIndex M d s i
        ∀ W : ParityWindow (activation h) ε → Set (Fin n),
          (∀ b, W b ⊆ nominalLayerSet M hE κ (groupMask M f s f.D)
            (groupMask M f s f.C) h (U : Set (Fin n)) ε b) →
          (∑ b, (W b).ncard) ≤ U.card / κ →
          (Set.toFinite (nominalResidualSet M hE κ (groupMask M f s f.D)
            (groupMask M f s f.C) (groupMask M f s f.T) h (U : Set (Fin n)) ε W)).toFinset ∈
              family

end MatroidProphet

end OAI
