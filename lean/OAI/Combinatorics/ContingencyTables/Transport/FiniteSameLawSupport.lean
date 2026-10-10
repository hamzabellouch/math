import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport

namespace OAI

/-! # Pointwise support transfer for finite uniform experiments -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

theorem SameLaw.property {X Y Z : Type*} [Fintype X] [Fintype Y]
    {f : X→Z} {g : Y→Z} (h : SameLaw f g) (P : Z→Prop)
    (hg : ∀ y,P (g y)) (x : X) : P (f x) := by
  by_contra hx
  let bad : Z→ℝ := fun z => if P z then 0 else 1
  have he := h bad
  have hz : uniformAverage (fun y => bad (g y))=0 := by
    simp only [bad,hg,ite_true,uniformAverage,Finset.sum_const_zero,zero_div]
  rw [hz] at he
  have hnonneg (t : X) : 0 ≤ bad (f t) := by
    dsimp only [bad]
    split_ifs <;> norm_num
  have hsum : (∑ t : X,bad (f t))=0 := by
    rcases (div_eq_zero_iff).mp he with he'|he'
    · exact he'
    · have hc : Fintype.card X≠0 := by
        let : Nonempty X := ⟨x⟩
        exact Fintype.card_ne_zero
      exact False.elim (hc (by exact_mod_cast he'))
  have hb := Finset.single_le_sum (fun t _ => hnonneg t) (Finset.mem_univ x)
  rw [hsum] at hb
  simp only [bad,hx,ite_false] at hb
  norm_num at hb

theorem SameLaw.exists_preimage {X Y Z : Type*} [Fintype X] [Fintype Y]
    {f : X→Z} {g : Y→Z} (h : SameLaw f g) (x : X) : ∃ y,g y=f x :=
  h.property (fun z => ∃ y,g y=z) (fun y => ⟨y,rfl⟩) x

end
end ContingencyTables.FiniteObservableTransport

end OAI
