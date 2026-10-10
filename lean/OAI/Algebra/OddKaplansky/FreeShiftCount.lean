import OAI.Algebra.OddKaplansky.WreathActions

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.FreeShiftCount
noncomputable section
open scoped Classical BigOperators
variable {X : Type portUniverse1} {C : Type portUniverse2} [Fintype X] [Fintype C]

lemma card_equal_coordinate (a b : X) (hab : a ≠ b) :
    Fintype.card {f : X → C // f a = f b} * Fintype.card C ≤ Fintype.card C ^ Fintype.card X := by
  let r : {f : X → C // f a = f b} → ({x : X // x ≠ a} → C) := fun f x => f.val x.val
  have hr : Function.Injective r := by
    intro f g he
    apply Subtype.ext
    funext x
    by_cases hx : x = a
    · subst x
      have he' : f.val b = g.val b := congrFun he ⟨b,Ne.symm hab⟩
      exact f.property.trans (he'.trans g.property.symm)
    · exact congrFun he ⟨x,hx⟩
  have hh := Fintype.card_le_of_injective r hr
  rw [Fintype.card_fun] at hh
  have hc := Fintype.card_congr (Equiv.optionSubtypeNe a)
  rw [Fintype.card_option] at hc
  calc
    _ ≤ Fintype.card C ^ Fintype.card {x : X // x ≠ a} * Fintype.card C := Nat.mul_le_mul_right _ hh
    _ = _ := by rw [← pow_succ,hc]

variable {H : Type portUniverse3} [Group H] [Fintype H]
def Free (f : H → C) : Prop := ∀ g : H, (∀ x, f (g⁻¹*x) = f x) → g = 1

lemma card_not_free :
    Fintype.card {f : H → C // ¬ Free f} * Fintype.card C ≤
      (Fintype.card H - 1) * Fintype.card C ^ Fintype.card H := by
  let F (g : H) := {f : H → C | ∀ x, f (g⁻¹*x) = f x}
  have hFg (g : H) (hg : g ≠ 1) : Fintype.card (F g) * Fintype.card C ≤ Fintype.card C ^ Fintype.card H := by
    have hi : Fintype.card (F g) ≤ Fintype.card {f : H → C // f 1 = f g⁻¹} := by
      apply Fintype.card_le_of_injective (fun f => ⟨f.val,by simpa using (f.property 1).symm⟩)
      intro f t he
      exact Subtype.ext (congrArg (fun q : {f : H → C // f 1 = f g⁻¹} => q.val) he)
    apply (Nat.mul_le_mul_right _ hi).trans
    exact card_equal_coordinate 1 g⁻¹ (by simpa using hg)
  let U := (Finset.univ.erase (1 : H)).biUnion (fun g => Finset.univ.filter (fun f : H → C => f ∈ F g))
  have hU : U = Finset.univ.filter (fun f : H → C => ¬ Free f) := by
    ext f
    simp only [U, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter,true_and,F,Set.mem_ofPred_eq,Free]
    simp only [not_forall]
    aesop
  have hcard : Fintype.card {f : H → C // ¬ Free f} = U.card := by
    rw [hU]
    exact Fintype.card_subtype _
  rw [hcard]
  calc
    U.card * Fintype.card C ≤ (∑ g ∈ Finset.univ.erase (1 : H), (Finset.univ.filter (fun f : H → C => f ∈ F g)).card) * Fintype.card C :=
      Nat.mul_le_mul_right _ (Finset.card_biUnion_le)
    _ = ∑ g ∈ Finset.univ.erase (1 : H), (Finset.univ.filter (fun f : H → C => f ∈ F g)).card * Fintype.card C := by rw [Finset.sum_mul]
    _ ≤ ∑ _g ∈ Finset.univ.erase (1 : H), Fintype.card C ^ Fintype.card H := by
      apply Finset.sum_le_sum
      intro g hg
      rw [← Fintype.card_subtype]
      exact hFg g (Finset.mem_erase.mp hg).1
    _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_univ (1 : H))]
end
end OddKaplansky.FreeShiftCount

end

end OAI
