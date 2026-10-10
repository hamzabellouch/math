import OAI.Analysis.Pureness.Divisibility.HereditarySplitting

namespace OAI
namespace CuntzPureness
open scoped ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_orthogonal_family_with_reserve (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) (N : ℕ) :
    ∃ r : A, ∃ a : Fin N → A,
      0 ≤ r ∧ r ≠ 0 ∧ (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≠ 0) ∧
      (∀ i j, i ≠ j → a i * a j = 0) ∧ (∀ i, a i * r = 0) := by
  induction N with
  | zero => exact ⟨h, Fin.elim0, hh, hh0, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨r, a, hr, hr0, ha, ha0, horth, har⟩ := ih
    obtain ⟨e, f, he, he0, hem, hf, hf0, hfm, hef⟩ :=
      exists_orthogonal_pair_hereditary τ hsimple hinf r hr hr0
    have hae (i : Fin N) : a i * e = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hem (har i)
    have hea (i : Fin N) : e * a i = 0 := by
      simpa only [star_mul, he.star_eq, (ha i).star_eq, star_zero] using congrArg star (hae i)
    have haf (i : Fin N) : a i * f = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hfm (har i)
    refine ⟨f, Fin.cons e a, hf, hf0, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact he
      | succ i => exact ha i
    · intro i
      cases i using Fin.cases with
      | zero => exact he0
      | succ i => exact ha0 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hea j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact hae i
        | succ j => exact horth i j (fun heq => hij (congrArg Fin.succ heq))
    · intro i
      cases i using Fin.cases with
      | zero => exact hef
      | succ i => exact haf i

theorem small_hereditary_rank (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      ∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞) := by
  classical
  rcases subsingleton_or_nontrivial A with hsub | hnontriv
  · let := hsub
    exact False.elim (hinf inferInstance)
  · let := hnontriv
    obtain ⟨τ⟩ := hT
    obtain ⟨r, a, hr, hr0, ha, ha0, horth, har⟩ :=
      exists_orthogonal_family_with_reserve τ hsimple hinf 1 zero_le_one one_ne_zero N
    obtain ⟨h, hh, hh0, hC, hR⟩ := small_rank_of_orthogonal_family hsimple N hN a ha ha0 horth
    exact ⟨h, hh, hh0, hR⟩
end CuntzPureness

end OAI
