import OAI.Combinatorics.Crossing.FinitePathChain

namespace OAI

noncomputable section
namespace Zarankiewicz

def alternatingPath (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → Path (a 0) (b n)
  | 0 => p 0
  | n+1 => ((alternatingPath a b p q n).trans (q n)).trans (p (n+1))

theorem alternatingPath_range_iff (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → ∀ x,
    x ∈ Set.range (alternatingPath a b p q n) ↔
      (∃ i, i ≤ n ∧ x ∈ Set.range (p i)) ∨ (∃ i, i < n ∧ x ∈ Set.range (q i))
  | 0, x => by
    constructor
    · intro h
      exact Or.inl ⟨0,le_rfl,h⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · have he : i=0 := by omega
        subst i
        exact h
      · omega
  | n+1, x => by
    rw [alternatingPath,Path.trans_range,Path.trans_range,Set.mem_union,Set.mem_union,
      alternatingPath_range_iff a b p q n]
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with ⟨i,hi,h⟩ | ⟨i,hi,h⟩
          · exact Or.inl ⟨i,by omega,h⟩
          · exact Or.inr ⟨i,by omega,h⟩
        · exact Or.inr ⟨n,by omega,hx⟩
      · exact Or.inl ⟨n+1,le_rfl,hx⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · by_cases he : i=n+1
        · subst i
          exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl ⟨i,by omega,h⟩))
      · by_cases he : i=n
        · subst i
          exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr ⟨i,by omega,h⟩))

theorem alternatingPath_injective (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) →
    (∀ i, i ≤ n → Function.Injective (p i)) → (∀ i, i < n → Function.Injective (q i)) →
    (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (Set.range (p i)) (Set.range (p j))) →
    (∀ i j, i < n → j < n → i ≠ j → Disjoint (Set.range (q i)) (Set.range (q j))) →
    (∀ i j, i ≤ n → j < n → ∀ x, x ∈ Set.range (p i) → x ∈ Set.range (q j) →
      (i=j ∧ x=b j) ∨ (i=j+1 ∧ x=a (j+1))) →
    Function.Injective (alternatingPath a b p q n)
  | 0, hp, _, _, _, _ => hp 0 le_rfl
  | n+1, hp, hq, hpp, hqq, hpq => by
    have hprev : Function.Injective (alternatingPath a b p q n) :=
      alternatingPath_injective a b p q n (fun i hi => hp i (by omega))
        (fun i hi => hq i (by omega)) (fun i j hi hj => hpp i j (by omega) (by omega))
        (fun i j hi hj => hqq i j (by omega) (by omega))
        (fun i j hi hj => hpq i j (by omega) (by omega))
    have hfirst : Function.Injective ((alternatingPath a b p q n).trans (q n)) := by
      apply path_trans_injective _ _ hprev (hq n (by omega))
      intro x hx hy
      rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · rcases hpq i n (by omega) (by omega) x hh hy with ⟨he,hx⟩ | ⟨he,hx⟩
        · exact hx
        · omega
      · exact False.elim (Set.disjoint_left.mp (hqq i n (by omega) (by omega) (by omega)) hh hy)
    apply path_trans_injective _ _ hfirst (hp (n+1) le_rfl)
    intro x hx hy
    rw [Path.trans_range] at hx
    rcases hx with hx | hx
    · rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · exact False.elim (Set.disjoint_left.mp (hpp i (n+1) (by omega) le_rfl (by omega)) hh hy)
      · rcases hpq (n+1) i le_rfl (by omega) x hy hh with ⟨he,hx⟩ | ⟨he,hx⟩ <;> omega
    · rcases hpq (n+1) n le_rfl (by omega) x hy hx with ⟨he,hx⟩ | ⟨he,hx⟩
      · omega
      · exact hx

end Zarankiewicz

end

end OAI
