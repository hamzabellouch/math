import OAI.NumberTheory.Ostmann.Arithmetic.GroupHaarImage

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators

theorem unit_haar_proportion {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f)
    (P : H → Prop) :
    (Nat.card {x:G // P (f x)}:ℝ)/Nat.card G =
      (Nat.card {y:H // P y}:ℝ)/Nat.card H := by
  classical
  have he := Arithmetic.GroupHaarImage.average_surjective f hf
    (fun y => if P y then (1:ℂ) else 0)
  have hsG : (∑x:G,if P (f x) then (1:ℂ) else 0)=
      (Nat.card {x:G // P (f x)}:ℂ) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsH : (∑y:H,if P y then (1:ℂ) else 0)=
      (Nat.card {y:H // P y}:ℂ) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold Arithmetic.ResidueHaar.average at he
  rw [hsG, hsH] at he
  have hh : (((Nat.card {x:G // P (f x)}:ℝ)/Nat.card G):ℂ)=
      (((Nat.card {y:H // P y}:ℝ)/Nat.card H):ℂ) := by
    push_cast
    simpa only [Nat.card_eq_fintype_card, div_eq_mul_inv, mul_comm] using he
  exact_mod_cast hh

end Ostmann.Characters

end

end OAI
