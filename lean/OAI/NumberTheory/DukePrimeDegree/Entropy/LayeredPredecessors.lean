import OAI.NumberTheory.DukePrimeDegree.Entropy.LayeredObservations

namespace OAI

/-! # Combining the three possible predecessor height levels -/

noncomputable section
open Set
namespace DukePrimeDegree

def UniformFinitePredecessors {Y : Type*} (T : Y → Y) (Q : Y → ℕ) : Prop :=
  ∃ M : ℕ, ∀ q : ℕ, ∃ F : Finset ℕ, Q '' {y | Q (T y)=q} ⊆ F ∧ F.card ≤ M

theorem uniformFinitePredecessors_of_height_layers {Y : Type*}
    (T : Y → Y) (H Q : Y → ℕ)
    (hstep : ∀ y, H (T y) ≤ H y+1 ∧ H y ≤ H (T y)+1)
    (hrefine : ∀ x y, Q y=Q x → H y=H x)
    (M : ℕ)
    (hlayer : ∀ q k : ℕ, ∃ F : Finset ℕ,
      Q '' {y | H y=k ∧ Q (T y)=q} ⊆ F ∧ F.card ≤ M) :
    UniformFinitePredecessors T Q := by
  classical
  refine ⟨3*M,?_⟩
  intro q
  by_cases he : ∃ x, Q (T x)=q
  · obtain ⟨x,hx⟩ := he
    let m := H (T x)
    choose F hF hcard using (hlayer q)
    let A := F (m-1) ∪ F m ∪ F (m+1)
    refine ⟨A,?_,?_⟩
    · rintro _ ⟨y,hy,rfl⟩
      have hyq : Q (T y)=q := hy
      have hym : H (T y)=m := hrefine (T x) (T y) (hyq.trans hx.symm)
      have hyk : H y=m-1 ∨ H y=m ∨ H y=m+1 := by
        have hs := hstep y
        dsimp [m] at hym ⊢
        omega
      rcases hyk with hyk | hyk | hyk
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact hF (m-1) ⟨y,⟨hyk,hyq⟩,rfl⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact hF m ⟨y,⟨hyk,hyq⟩,rfl⟩
      · apply Finset.mem_union_right
        exact hF (m+1) ⟨y,⟨hyk,hyq⟩,rfl⟩
    · have h₁ := Finset.card_union_le (F (m-1)) (F m)
      have h₂ := Finset.card_union_le (F (m-1) ∪ F m) (F (m+1))
      have hprev := hcard (m-1)
      have hm := hcard m
      have hnext := hcard (m+1)
      change (F (m-1) ∪ F m ∪ F (m+1)).card ≤ 3*M
      omega
  · refine ⟨∅,?_,by simp⟩
    rintro _ ⟨y,hy,_⟩
    exact (he ⟨y,hy⟩).elim

end DukePrimeDegree

end

end OAI
