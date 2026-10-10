import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPageCRT

namespace OAI

/-! # Both giant prime coordinates in the exact arithmetic CRT average -/

namespace Ostmann
open scoped Classical BigOperators

/-- Restricting the first external CRT coordinate to a unit gives the
original two-prime CRT coordinates. -/
theorem crtUnitPairEquiv_to_external {B : Type*} [Fintype B] (a : B → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (z : (ZMod (∏ i, a i))ˣ × (ZMod (∏ i, a i))ˣ) (i : B) :
    crtExternalPairEquiv a hc ((z.1 : ZMod (∏ i, a i)), z.2) i =
      ((crtUnitPairEquiv a hc z i).1.val, (crtUnitPairEquiv a hc z i).2) := by
  rcases z with ⟨x, y⟩
  simp only [crtExternalPairEquiv_apply, crtUnitPairEquiv_apply,
    crtUnitEquiv_apply, ZMod.prodEquivPi_apply]
  rfl

/-- Both Page factors stay in the frequency block; the other blocks have
exactly their uniform two-unit laws. -/
noncomputable def movingArithmeticPrimePageFactor {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ) :
    ∀ b, (ZMod (movingArithmeticModuli r q P S b))ˣ ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ
  | .inl u, z => f (.inl u) (z.1.val, z.2) *
      pageGiantWeight input Q r (show (ZMod r)ˣ from z.1).val.val x *
      pageGiantWeight input Q r (show (ZMod r)ˣ from z.2).val.val y
  | .inr b, z => f (.inr b) (z.1.val, z.2)

theorem movingArithmeticPrimePageFactor_product {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ)
    (v : ∀ b, (ZMod (movingArithmeticModuli r q P S b))ˣ ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) :
    (∏ b, movingArithmeticPrimePageFactor r q P S input Q x y f b (v b)) =
      (∏ b, f b ((v b).1.val, (v b).2)) *
        pageGiantWeight input Q r
          (show (ZMod r)ˣ from (v (.inl ())).1).val.val x *
        pageGiantWeight input Q r
          (show (ZMod r)ˣ from (v (.inl ())).2).val.val y := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPrimePageFactor]
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

/-- The literal two-prime giant average, with both exceptional-character
multipliers, factors over the same concrete arithmetic blocks. -/
theorem movingSeparatedPairResidueCoefficient_prime_page_average (x y : ℝ) :
    correctedPrimePairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) x y =
    ∏ b, (Fintype.card ((ZMod (movingArithmeticModuli r q P S b))ˣ ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPrimePageFactor r q P S input Q x y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z := by
  let a := movingArithmeticModuli r q P S
  let e := crtUnitPairEquiv a hc
  let f := movingArithmeticLocalFactor q value outside F E g D T nodes R r P S
  let fP := movingArithmeticPrimePageFactor r q P S input Q x y f
  have hpageA : pageAtModulus (∏ b, a b) (selectedPageZero input Q) =
      pageAtModulus r (selectedPageZero input Q) := hpage
  have he (z : (ZMod (∏ b, a b))ˣ × (ZMod (∏ b, a b))ˣ) :
      movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
          z.1.val.val z.2.val.val *
        pageGiantWeight input Q (∏ b, a b) z.1.val.val x *
        pageGiantWeight input Q (∏ b, a b) z.2.val.val y =
      ∏ b, fP b (e z b) := by
    have hp (i : Bool) (w : ℝ) :
        pageGiantWeight input Q (∏ b, a b) (if i then z.1.val.val else z.2.val.val) w =
        pageGiantWeight input Q r
          (if i then (e z (.inl ())).1.val.val else (e z (.inl ())).2.val.val) w := by
      have hcast := crtExternalPairEquiv_casts a hc (z.1.val, z.2) (.inl ())
      rw [crtUnitPairEquiv_to_external] at hcast
      have hm : Nat.ModEq r (if i then z.1.val.val else z.2.val.val)
          (if i then (e z (.inl ())).1.val.val else (e z (.inl ())).2.val.val) := by
        apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        cases i
        · change (z.2.val.val : ZMod r) = ((e z (.inl ())).2.val.val : ZMod r)
          calc
            _ = (show ZMod r from (e z (.inl ())).2.val) := congrArg Prod.snd hcast
            _ = _ := (ZMod.natCast_zmod_val (show ZMod r from (e z (.inl ())).2.val)).symm
        · change (z.1.val.val : ZMod r) = ((e z (.inl ())).1.val.val : ZMod r)
          calc
            _ = (show ZMod r from (e z (.inl ())).1.val) := congrArg Prod.fst hcast
            _ = _ := (ZMod.natCast_zmod_val (show ZMod r from (e z (.inl ())).1.val)).symm
      calc
        _ = pageGiantWeight input Q r (if i then z.1.val.val else z.2.val.val) w := by
          simp only [pageGiantWeight, hpageA]
        _ = _ := pageGiantWeight_modEq input Q r _ _ hm w
    have hleft := hp true x
    have hright := hp false y
    simp only [ite_true, Bool.false_eq_true, ite_false] at hleft hright
    rw [movingSeparatedPairResidueCoefficient_crt q value outside F E g D T nodes
      R r P S hf hR hfrequency hcover hc (z.1.val, z.2), hleft, hright]
    simp_rw [crtUnitPairEquiv_to_external]
    exact (movingArithmeticPrimePageFactor_product r q P S input Q x y f (e z)).symm
  unfold correctedPrimePairAverage
  have hsum : (∑ z : (ZMod (∏ b, a b))ˣ × (ZMod (∏ b, a b))ˣ,
      movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
        z.1.val.val z.2.val.val *
        pageGiantWeight input Q (∏ b, a b) z.1.val.val x *
        pageGiantWeight input Q (∏ b, a b) z.2.val.val y) =
      ∑ z : (ZMod (∏ b, a b))ˣ × (ZMod (∏ b, a b))ˣ, ∏ b, fP b (e z b) :=
    Finset.sum_congr rfl (fun z _ => he z)
  rw [hsum, e.sum_comp (fun z => ∏ b, fP b (z b)), Fintype.card_congr e, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rfl

end
end Ostmann

end OAI
