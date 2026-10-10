import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedCRT
import OAI.NumberTheory.Ostmann.ZeroDensity.PageRegularAverage

namespace OAI

/-! # Retaining the Page correction in the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingArithmeticPageFactor {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ) :
    ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ
  | .inl u, z => f (.inl u) z *
      pageGiantWeight input Q r (show (ZMod r)ˣ from z.2).val.val y
  | .inr b, z => f (.inr b) z

theorem movingArithmeticPageFactor_product {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ)
    (v : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) :
    (∏ b, movingArithmeticPageFactor r q P S input Q y f b (v b)) =
      (∏ b, f b (v b)) *
        pageGiantWeight input Q r
          (show (ZMod r)ˣ from (v (.inl ())).2).val.val y := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPageFactor]
  ring

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [∀ b, NeZero (movingArithmeticModuli r q P S b)]
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))
  (input : PublishedProgressionInput) (Q : ℕ)
  (hpage : pageAtModulus (∏ b, movingArithmeticModuli r q P S b) (selectedPageZero input Q) =
    pageAtModulus r (selectedPageZero input Q))

include hf hR hfrequency hcover hc hpage

/-- The original Page-weighted mixed average factors exactly. Its Page term
stays in the frequency factor, with no absolute value or mean replacement. -/
theorem movingSeparatedPairResidueCoefficient_page_average (y : ℝ) :
    correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) y =
    ∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPageFactor r q P S input Q y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z := by
  let a := movingArithmeticModuli r q P S
  let e := crtExternalPairEquiv a hc
  let f := movingArithmeticLocalFactor q value outside F E g D T nodes R r P S
  let fP := movingArithmeticPageFactor r q P S input Q y f
  have hpageA : pageAtModulus (∏ b, a b) (selectedPageZero input Q) =
      pageAtModulus r (selectedPageZero input Q) := hpage
  have he (z : ZMod (∏ b, a b) × (ZMod (∏ b, a b))ˣ) :
      movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
          z.1.val (z.2 : ZMod (∏ b, a b)).val *
        pageGiantWeight input Q (∏ b, a b) (z.2 : ZMod (∏ b, a b)).val y =
      ∏ b, fP b (e z b) := by
    have hcast := crtExternalPairEquiv_casts a hc z (.inl ())
    let v : ZMod r × (ZMod r)ˣ := e z (.inl ())
    have hm : Nat.ModEq r (z.2 : ZMod (∏ b, a b)).val (v.2 : ZMod r).val := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      have hh : ((z.2 : ZMod (∏ b, a b)).val : ZMod r) = (v.2 : ZMod r) :=
        congrArg Prod.snd hcast
      simpa only [ZMod.natCast_zmod_val] using hh
    have hp : pageGiantWeight input Q (∏ b, a b) (z.2 : ZMod (∏ b, a b)).val y =
        pageGiantWeight input Q r (v.2 : ZMod r).val y := by
      calc
        _ = pageGiantWeight input Q r (z.2 : ZMod (∏ b, a b)).val y := by
          simp only [pageGiantWeight, hpageA]
        _ = _ := pageGiantWeight_modEq input Q r _ _ hm y
    rw [movingSeparatedPairResidueCoefficient_crt q value outside F E g D T nodes
      R r P S hf hR hfrequency hcover hc, hp]
    exact (movingArithmeticPageFactor_product r q P S input Q y f (e z)).symm
  unfold correctedMixedPairAverage
  calc
    _ = (Fintype.card (ZMod (∏ b, a b) × (ZMod (∏ b, a b))ˣ) : ℂ)⁻¹ *
        (∑ z, ∏ b, fP b (e z b)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      exact he z
    _ = _ := movingArithmeticBlocks_average r q P S hc fP

end
end Ostmann

end OAI
