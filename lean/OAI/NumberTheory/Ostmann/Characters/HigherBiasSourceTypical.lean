import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Ostmann.Preliminaries Ostmann.Construction Filter
open scoped BigOperators

def higherSourceTypicalEndpoints {ι : Type*} [Fintype ι]
    (d : Decomposition) (X : ℕ) {δ : ℝ}
    {E : Finset (PrimeUpTo (collisionScale 10 X))}
    (F : HigherBiasSourceFamily d (collisionScale 10 X) E δ)
    (G : ι → Finset (PrimeUpTo (collisionScale 10 X)))
    (hm : ∀ i,0 < primeShellMass (G i)) : Finset ℕ :=
  (upperWindow d.A X).filter (fun a => ∀ i,
    δ/2 ≤ ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (a:ZMod p.val))).re)

theorem eventually_higherSourceTypical_count (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop,∀ (ι : Type) [Fintype ι],∀ δ : ℝ,0 < δ →
      ∀ E : Finset (PrimeUpTo (collisionScale 10 X)),
      ∀ F : HigherBiasSourceFamily d (collisionScale 10 X) E δ,
      ∀ G : ι → Finset (PrimeUpTo (collisionScale 10 X)),
      (∀ i,G i ⊆ E) → ∀ hm : ∀ i,0 < primeShellMass (G i),
      ∀ Λ : ℝ,0 < Λ →
      (∀ i,∀ p∈G i,Λ ≤ Real.log p.val) →
      (∀ i,(primeShellMass (G i)*Λ)⁻¹ *
        (collisionConstant 10*Real.log (Real.log (X:ℝ))) < (δ/2)^2) →
      ((upperWindow d.A X).card:ℝ) ≤
        (higherSourceTypicalEndpoints d X F G hm).card +
          (Fintype.card ι:ℝ)*Real.sqrt X/(Real.log (X:ℝ))^10 := by
  classical
  filter_upwards [eventually_few_bad_shell_endpoints d 10 (by norm_num)] with X hbad
  intro ι _ δ hδ E F G hG hm Λ hΛ hscale hsmall
  let P : ι → ℕ → Prop := fun i a =>
    δ/2 ≤ ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (a:ZMod p.val))).re
  have hi : ∀ i,(((upperWindow d.A X).filter (fun a => ¬P i a)).card:ℝ) ≤
      Real.sqrt X/(Real.log (X:ℝ))^10 := by
    intro i
    have hh := hbad (G i) (hm i) Λ δ hΛ hδ (hscale i) (hsmall i) F.test
      F.test_norm_le_one (F.shell_residue_mean_lower (G i) (hG i) (hm i))
    simpa only [P,not_le] using hh.le
  have hb := simultaneous_bad_count (upperWindow d.A X) P _ hi
  have hpartition : (upperWindow d.A X).card =
      (higherSourceTypicalEndpoints d X F G hm).card +
        ((upperWindow d.A X).filter (fun a => ¬∀ i,P i a)).card := by
    exact (Finset.card_filter_add_card_filter_not (s := upperWindow d.A X) (fun a => ∀ i,P i a)).symm
  rw [hpartition,Nat.cast_add]
  have he : (Fintype.card ι:ℝ)*(Real.sqrt X/(Real.log (X:ℝ))^10) =
      (Fintype.card ι:ℝ)*Real.sqrt X/(Real.log (X:ℝ))^10 := by ring
  rw [he] at hb
  exact add_le_add_right hb _

end Ostmann.Characters

end

end OAI
