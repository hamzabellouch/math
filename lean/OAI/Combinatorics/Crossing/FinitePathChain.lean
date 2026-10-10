import OAI.Combinatorics.Crossing.PathConcatenationInjective

namespace OAI

noncomputable section
namespace Zarankiewicz

def finitePathChain (v : ℕ → Plane) (p : ∀ i, Path (v i) (v (i+1))) : (n : ℕ) → Path (v 0) (v n)
  | 0 => Path.refl (v 0)
  | 1 => p 0
  | n+2 => (finitePathChain v p (n+1)).trans (p (n+1))

theorem finitePathChain_range_iff (v : ℕ → Plane) (p : ∀ i, Path (v i) (v (i+1))) :
    (n : ℕ) → 0 < n → ∀ x, x ∈ Set.range (finitePathChain v p n) ↔
      ∃ i, i < n ∧ x ∈ Set.range (p i)
  | 0, hn, _ => by omega
  | 1, _, x => by
    constructor
    · intro h
      exact ⟨0,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      have he : i=0 := by omega
      subst i
      exact h
  | n+2, _, x => by
    rw [finitePathChain,Path.trans_range,Set.mem_union,finitePathChain_range_iff v p (n+1) (by omega)]
    constructor
    · rintro (⟨i,hi,h⟩ | h)
      · exact ⟨i,by omega,h⟩
      · exact ⟨n+1,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      by_cases hin : i < n+1
      · exact Or.inl ⟨i,hin,h⟩
      · have he : i=n+1 := by omega
        subst i
        exact Or.inr h

theorem finitePathChain_injective (v : ℕ → Plane) (p : ∀ i, Path (v i) (v (i+1))) :
    (n : ℕ) → 0 < n → (∀ i, i < n → Function.Injective (p i)) →
    (∀ i j, i < j → j < n → ∀ x, x ∈ Set.range (p i) → x ∈ Set.range (p j) →
      j=i+1 ∧ x=v j) → Function.Injective (finitePathChain v p n)
  | 0, hn, _, _ => by omega
  | 1, _, hp, _ => hp 0 (by omega)
  | n+2, _, hp, hm => by
    apply path_trans_injective
    · exact finitePathChain_injective v p (n+1) (by omega)
        (fun i hi => hp i (by omega)) (fun i j hij hj => hm i j hij (by omega))
    · exact hp (n+1) (by omega)
    · intro x hx hy
      obtain ⟨i,hi,hh⟩ := (finitePathChain_range_iff v p (n+1) (by omega) x).mp hx
      exact (hm i (n+1) hi (by omega) x hh hy).2

end Zarankiewicz

end

end OAI
