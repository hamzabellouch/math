import OAI.Probability.GammaPassage.ContourLocalization

namespace OAI

/-! The explicit C(m+1)^2 4^m encoding bound from cr:oriented-paths. -/
namespace PlanarFPP
open Finset

namespace SquareLoop
variable {m : ℕ}

theorem eq_of_start_direction (c d : SquareLoop m) (hm : 0 < m)
    (h0 : (c.side ⟨0,hm⟩).tail = (d.side ⟨0,hm⟩).tail)
    (hd : ∀ i, (c.side i).2 = (d.side i).2) : c = d := by
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hp (i : Fin m) : (c.side i).tail = (d.side i).tail := by
    obtain ⟨n,hn⟩ := i
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hn' : n < m := by omega
      have hr : finRotate m ⟨n,hn'⟩ = ⟨n+1,hn⟩ := by
        apply Fin.ext
        simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt hn
      have hc := c.follows ⟨n,hn'⟩
      have hh := d.follows ⟨n,hn'⟩
      rw [hr] at hc hh
      rw [hc,hh,SquareSide.head,SquareSide.head,ih hn',hd]
  have he : c.side = d.side := by
    funext i
    apply Prod.ext
    · have hh := hp i
      change (c.side i).1 + (c.side i).2.corner =
        (d.side i).1 + (d.side i).2.corner at hh
      rw [hd] at hh
      exact add_right_cancel hh
    · exact hd i
  cases c
  cases d
  cases he
  rfl

end SquareLoop

/-- Length n+1 avoids a spurious zero-length contour in the countable union. -/
abbrev EnclosingLoop (n : ℕ) :=
  {c : SquareLoop (n+1) // c.winding ≠ 0 ∧ c.NoRepeatedSides}

def enclosingLoopCode (n : ℕ) (c : EnclosingLoop n) :
    {p // p ∈ orientedSelectionBox (n+2)} × (Fin (n+1) → Step) :=
  (⟨(c.val.side ⟨0,by omega⟩).tail,c.val.start_mem_box (by omega) c.property.1⟩,
    fun i => (c.val.side i).2)

theorem enclosingLoopCode_injective (n : ℕ) : Function.Injective (enclosingLoopCode n) := by
  intro c d h
  apply Subtype.ext
  apply SquareLoop.eq_of_start_direction c.val d.val (by omega)
  · exact congrArg (fun x => x.1.val) h
  · intro i
    exact congrArg (fun x => x.2 i) h

noncomputable instance enclosingLoopFintype (n : ℕ) : Fintype (EnclosingLoop n) :=
  Fintype.ofInjective (enclosingLoopCode n) (enclosingLoopCode_injective n)

/-- At most 9(m+1)^2 4^m enclosing loops of length m = n+1, with indexed
starting side; counting these also bounds unrooted contours. -/
theorem enclosingLoop_card (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*(n+2)^2*4^(n+1) := by
  have hh := Fintype.card_le_of_injective _ (enclosingLoopCode_injective n)
  have hf : Fintype.card Step = 4 := by decide
  simp only [Fintype.card_prod, Fintype.card_coe, orientedSelectionBox_card,
    Fintype.card_fun, Fintype.card_fin, hf] at hh
  have hsq : (2*(n+2)+1)^2 ≤ 9*(n+2)^2 := by
    calc
      _ ≤ (3*(n+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  exact hh.trans (Nat.mul_le_mul_right _ hsq)

end PlanarFPP

end OAI
