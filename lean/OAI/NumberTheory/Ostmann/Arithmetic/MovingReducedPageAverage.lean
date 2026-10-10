import OAI.NumberTheory.Ostmann.ZeroDensity.PageRegularAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularCoprime

namespace OAI

/-! # The Page-weighted regular average of the actual two-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

/-- All non-Page hypotheses here are the actual small-slot and tree data. The
periodicity and regular-block coprimality are derived from those data. -/
theorem movingReducedPair_regular_page_average {σ I J : Type*} [Fintype J] [DecidableEq J]
    (P : PublishedProgressionInput) (N : ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hout : ∀ b, movingRegularOutsidePairwise value outside (T b))
    (reg : J → ℕ) [∀ i, Fact (reg i).Prime] [∀ i, NeZero (reg i)] [NeZero (∏ i, reg i)]
    (hreg : Pairwise (fun i j => (reg i).Coprime (reg j)))
    (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
    (hq : ∀ i ∈ S, (∏ j, reg j).Coprime (q i))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, reg i) * r)]
    (hr : r = movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside
      childBound pivotBound T hf q S)
    (hpage : pageAtModulus ((∏ i, reg i) * r) (selectedPageZero P N) =
      pageAtModulus r (selectedPageZero P N))
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (reg i))
    (hs : ∀ i, (s : ZMod (reg i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (greg : ∀ i, ZMod (reg i) → ℂ) (hg : ∀ i, greg i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) (y : ℝ) :
    let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound (hf b) (.prime false) (.prime true)
    let C := movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
    correctedMixedPairAverage P N ((∏ i, reg i) * r)
      (fun a b => C a b * (guardedRegularMultiplier reg active s other greg a b : ℂ)) y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P N r C y := by
  dsimp only
  have hcop : (∏ i, reg i).Coprime r := by
    rw [hr]
    exact movingOriginalRegular_coprime_reduced tier value hprime hdisjoint outside childBound
      pivotBound T hf hlevels hsmall hout (∏ i, reg i) hregular q S hq
  apply periodic_coefficient_regular_page_average P N reg hreg r hcop hpage
    active s other hs ho greg hg henergy
  intro a b c d hab hcd
  apply movingReducedPairResidueCoefficient_modEq q value (fun i => (hprime i).ne_zero)
    outside childBound pivotBound F E g Dq S T hf a b c d
  · rw [← hr]
    exact Int.natCast_modEq_iff.mpr hab
  · rw [← hr]
    exact Int.natCast_modEq_iff.mpr hcd

end Ostmann

end OAI
