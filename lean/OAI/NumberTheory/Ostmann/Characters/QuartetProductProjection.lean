import OAI.NumberTheory.Ostmann.Characters.QuartetStateBounds
import OAI.NumberTheory.Ostmann.Characters.HeldCycleAverage

namespace OAI

/-! # Cycle projection of a product of actual quartet states -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetProjectionCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance quartetProjectionCharDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

noncomputable def quartetStateProduct {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] (g : ZMod p → ℂ) (D : (ZMod p)ˣ)
    (S : I → RationalQuartetState p) (P : I → (ZMod p)ˣ) (choice : I → QuartetMovingCase)
    (h : I → (ZMod p)ˣ × (ZMod p)ˣ) (r : I → (ZMod p)ˣ) : ℂ :=
  ∏ i : I, rationalQuartetStateAmplitude g D (S i)
    (quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i))

theorem quartetStateProduct_projection_le {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ)
    (S : I → RationalQuartetState p) (P : I → (ZMod p)ˣ)
    (cL cR : I → Bool)
    (hc : ∀ i, (S i).conjugations = ((cL i, !(cL i)), (cR i, !(cR i))))
    (choice : I → QuartetMovingCase) (sign : I → ℤ) :
    ((Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ h : I → (ZMod p)ˣ × (ZMod p)ˣ,
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ r : I → (ZMod p)ˣ,
            ‖cycleAverage sign (quartetStateProduct g D S P choice h) r‖ ^ 2) ≤
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, quartetMovingMajorant g (cL i) (cR i) (choice i) (ρ i)
            (rationalQuartetStateArgument D (S i) (P i)) else 0 := by
  classical
  unfold quartetStateProduct
  apply held_cycle_product_energy_le
    (fun i (h : (ZMod p)ˣ × (ZMod p)ˣ) r => rationalQuartetStateAmplitude g D (S i)
      (quartetMovingLeaves (choice i) (P i) h.1 h.2 r)) sign
      (fun i ρ => quartetMovingMajorant g (cL i) (cR i) (choice i) ρ
        (rationalQuartetStateArgument D (S i) (P i)))
  intro i ρ
  have h := rationalTree_quartet_coefficient_le g D (S i).tree
    (S i).XL (S i).XR (P i) (cL i) (cR i) (choice i) ρ
  unfold rationalQuartetStateAmplitude rationalQuartetStateArgument
  rw [hc i]
  simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    mul_inv_rev, Finset.mul_sum, mul_assoc] using h

end Ostmann

end OAI
