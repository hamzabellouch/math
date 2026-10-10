import OAI.MeasureTheory.Falconer.Estimates.ScalarSwitchProgression

namespace OAI

/-! Finite scalar branching with a reserved separation margin. This
 records exactly the tail-motion bookkeeping of the nonporous argument. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_branch_union_separated {α : Type*} (v : α → ℝ) (S : Finset α)
    (F : α → Finset α) {D ρ r : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → D ≤ |v x-v y|)
    (hF : ∀ x ∈ S, ∀ y ∈ F x, ∀ z ∈ F x, y ≠ z → ρ ≤ |v y-v z|)
    (hm : ∀ x ∈ S, ∀ y ∈ F x, |v y-v x| ≤ r)
    (hgap : ρ+2*r ≤ D) :
    ∀ y ∈ S.biUnion F, ∀ z ∈ S.biUnion F, y ≠ z → ρ ≤ |v y-v z| := by
  intro y hy z hz hyz
  obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨w,hw,hz⟩ := Finset.mem_biUnion.mp hz
  by_cases hxw : x = w
  · subst w
    exact hF x hx y hy z hz hyz
  · have h0 := hS x hx w hw hxw
    have h1 := hm x hx y hy
    have h2 := hm w hw z hz
    have ht : |v x-v w| ≤ |v y-v x|+|v y-v z|+|v z-v w| := by
      calc
        _ ≤ |v x-v y|+|v y-v w| := abs_sub_le _ _ _
        _ ≤ |v x-v y|+(|v y-v z|+|v z-v w|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm (v x) (v y)]; ring
    linarith

 theorem scalar_branch_union_card {α : Type*} (v : α → ℝ) (S : Finset α)
    (F : α → Finset α) (J : ℕ) {D r : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → D ≤ |v x-v y|)
    (hcard : ∀ x ∈ S, (F x).card = J)
    (hm : ∀ x ∈ S, ∀ y ∈ F x, |v y-v x| ≤ r)
    (hgap : 2*r < D) : (S.biUnion F).card = S.card*J := by
  have hd : (S : Set α).PairwiseDisjoint F := by
    intro x hx w hw hxw
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have h0 := hS x hx w hw hxw
    have h1 := hm x hx y hy
    have h2 := hm w hw y hz
    have ht : |v x-v w| ≤ |v y-v x|+|v y-v w| := by
      simpa only [abs_sub_comm (v x) (v y)] using abs_sub_le (v x) (v y) (v w)
    linarith
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _x ∈ S, J := Finset.sum_congr rfl (fun x hx => hcard x hx)
    _ = _ := by simp

 theorem scalar_finite_branch_growth {α : Type*} (v : α → ℝ) (P : ℕ → α → Prop)
    (N J : ℕ) (r b : ℕ → ℝ) (root : α) (hroot : P 0 root)
    (hb : ∀ n ≤ N, 0 < b n)
    (hgap : ∀ n < N, b (n+1)+2*r n ≤ b n)
    (hstep : ∀ n < N, ∀ x, P n x → ∃ F : Finset α,
      F.card = J ∧ (∀ y ∈ F, P (n+1) y) ∧
      (∀ y ∈ F, |v y-v x| ≤ r n) ∧
      (∀ y ∈ F, ∀ z ∈ F, y ≠ z → b (n+1) ≤ |v y-v z|)) :
    ∃ S : Finset α, S.card = J^N ∧ (∀ x ∈ S, P N x) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → b N ≤ |v x-v y| := by
  suffices hh : ∀ n ≤ N, ∃ S : Finset α, S.card = J^n ∧ (∀ x ∈ S, P n x) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → b n ≤ |v x-v y| from hh N le_rfl
  intro n hn
  induction n with
  | zero =>
    refine ⟨{root},by simp,?_,?_⟩
    · intro x hx
      simpa only [Finset.mem_singleton.mp hx] using hroot
    · intro x hx y hy hne
      exact False.elim (hne ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm))
  | succ n ih =>
    obtain ⟨S,hcard,hP,hsep⟩ := ih (by omega)
    have hnN : n < N := by omega
    have hex : ∀ x, ∃ F : Finset α, x ∈ S →
        F.card = J ∧ (∀ y ∈ F, P (n+1) y) ∧
        (∀ y ∈ F, |v y-v x| ≤ r n) ∧
        (∀ y ∈ F, ∀ z ∈ F, y ≠ z → b (n+1) ≤ |v y-v z|) := by
      intro x
      by_cases hx : x ∈ S
      · obtain ⟨F,hF⟩ := hstep n hnN x (hP x hx)
        exact ⟨F,fun _ => hF⟩
      · exact ⟨∅,fun h => False.elim (hx h)⟩
    choose F hF using hex
    have hmotion := fun x hx => (hF x hx).2.2.1
    have hchildren := fun x hx => (hF x hx).2.2.2
    refine ⟨S.biUnion F,?_,?_,?_⟩
    · rw [scalar_branch_union_card v S F J hsep (fun x hx => (hF x hx).1)
        hmotion (by have := hb (n+1) hn; have := hgap n hnN; linarith),hcard,pow_succ]
    · intro y hy
      obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
      exact (hF x hx).2.1 y hy
    · exact scalar_branch_union_separated v S F hsep hchildren hmotion (hgap n hnN)

end Falconer

end OAI
