import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialPathChildren
import OAI.MeasureTheory.Falconer.Measures.ScalarPrefixPruning

namespace OAI

/-! A single local choice for every occupied parent. Both the collapsed
 and branching alternatives have a dyadic child count and finite tags. -/
namespace Falconer.Regularization

def ScalarChildChoice (L : Finset (CellPath 1)) (a b : ℕ) (p : CellPath 1)
    (K : Finset (CellPath 1)) (k n : ℕ) : Prop :=
  K ⊆ prefixChildren L a b p ∧ K.card = 2^k ∧ k ≤ b-a ∧ a ≤ n ∧ n ≤ b ∧
    (prefixChildren L a b p).card ≤ 2050*K.card ∧
    (k = 0 ∨ (a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ K, ∀ r ∈ K, q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ K, ∃ r ∈ K, q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n))

 theorem exists_scalar_child_choice {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N)
    (p : CellPath 1) (hp : p ∈ L.image (List.take a)) :
    ∃ K k n, ScalarChildChoice L a b p K k n := by
  classical
  let C := prefixChildren L a b p
  by_cases hlarge : 2050 ≤ C.card
  · obtain ⟨K,hK,k,n,hk,hcard,hkeep,hn0,hn1,hsep,hpair⟩ :=
      scalar_initial_path_children L hL hab hb p hlarge
    have hkB : k ≤ b-a := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      rw [← hcard]
      exact (Finset.card_le_card hK).trans (scalar_prefix_children_card_le hL hab hb p)
    exact ⟨K,k,n,hK,hcard,hkB,by omega,by omega,hkeep,Or.inr ⟨hn0,hn1,hsep,hpair⟩⟩
  · have hCn : C.Nonempty := (prefixFiber_nonempty hp).image (List.take b)
    obtain ⟨q,hq⟩ := hCn
    refine ⟨{q},0,a,Finset.singleton_subset_iff.mpr hq,by simp,by omega,le_rfl,hab,?_,Or.inl rfl⟩
    simp only [Finset.card_singleton,mul_one]
    change C.card ≤ 2050
    omega

end Falconer.Regularization

end OAI
