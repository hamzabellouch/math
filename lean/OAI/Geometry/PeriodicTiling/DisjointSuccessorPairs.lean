import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace OAI

universe uV

namespace PeriodicTilingThree

private theorem exists_successor_anchors {V : Type uV} [Fintype V] [DecidableEq V]
    (τ : Equiv.Perm V) (hτ : ∀ v, τ v ≠ v) (marked : V) (k : ℕ)
    (hcard : 3 * (k + 1) ≤ Fintype.card V) :
    ∃ M : Finset V, M.card = k ∧
      (∀ u ∈ M, u ≠ marked ∧ τ u ≠ marked) ∧
      ∀ u ∈ M, ∀ v ∈ M, u ≠ τ v := by
  revert hcard
  induction k with
  | zero =>
      intro _
      refine ⟨∅, rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
      intro hcard
      obtain ⟨M, hM, hmarked, hseparated⟩ := ih (by omega)
      let B : Finset V := insert marked (insert (τ.symm marked)
        ((M ∪ M.image τ) ∪ M.image τ.symm))
      have hB : B.card ≤ 3 * k + 2 := by
        have hi₁ : (M.image τ).card ≤ M.card := Finset.card_image_le
        have hi₂ : (M.image τ.symm).card ≤ M.card := Finset.card_image_le
        have hu₁ := Finset.card_union_le M (M.image τ)
        have hu₂ := Finset.card_union_le (M ∪ M.image τ) (M.image τ.symm)
        have ha₁ := Finset.card_insert_le (τ.symm marked)
          ((M ∪ M.image τ) ∪ M.image τ.symm)
        have ha₂ := Finset.card_insert_le marked (insert (τ.symm marked)
          ((M ∪ M.image τ) ∪ M.image τ.symm))
        dsimp only [B]
        omega
      have hBlt : B.card < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]
        omega
      obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hBlt
      have hxM : x ∉ M := by
        intro h
        exact hx (by simp [B, h])
      have hximage : x ∉ M.image τ := by
        intro h
        exact hx (by simp [B, h])
      have hxpreimage : x ∉ M.image τ.symm := by
        intro h
        exact hx (by simp [B, h])
      have hxmarked : x ≠ marked := by
        intro h
        exact hx (by simp [B, h])
      have hτxmarked : τ x ≠ marked := by
        intro h
        have he : x = τ.symm marked := by
          rw [← h]
          exact (τ.symm_apply_apply x).symm
        exact hx (by simp [B, he])
      refine ⟨insert x M, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hxM, hM]
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨hxmarked, hτxmarked⟩
        · exact hmarked u hu
      · intro u hu v hv
        rcases Finset.mem_insert.mp hu with hux | huM
        · subst u
          rcases Finset.mem_insert.mp hv with hvx | hvM
          · subst v
            exact (hτ x).symm
          · intro he
            exact hximage (Finset.mem_image.mpr ⟨v, hvM, he.symm⟩)
        · rcases Finset.mem_insert.mp hv with hvx | hvM
          · subst v
            intro he
            apply hxpreimage
            refine Finset.mem_image.mpr ⟨u, huM, ?_⟩
            rw [he, τ.symm_apply_apply]
          · exact hseparated u huM v hvM

theorem exists_disjoint_successor_pairs {V : Type uV} [Fintype V]
    (τ : Equiv.Perm V) (hτ : ∀ v, τ v ≠ v) (marked : V) (k : ℕ)
    (hcard : 3 * (k + 1) ≤ Fintype.card V) :
    ∃ pair : (Fin k × Fin 2) ↪ V,
      (∀ j, pair (j, 1) = τ (pair (j, 0))) ∧ ∀ x, pair x ≠ marked := by
  classical
  obtain ⟨M, hM, hmarked, hseparated⟩ :=
    exists_successor_anchors τ hτ marked k hcard
  let e : Fin k ≃ ↥M := (Finset.equivFinOfCardEq hM).symm
  let a : Fin k → V := fun j => (e j : V)
  have ha : Function.Injective a := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  have hamem (j : Fin k) : a j ∈ M := (e j).property
  let f : Fin k × Fin 2 → V :=
    fun p => if p.2 = 0 then a p.1 else τ (a p.1)
  have hf : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    fin_cases b <;> fin_cases c
    · have hij : i = j := ha (by simpa [f] using h)
      cases hij
      rfl
    · exact False.elim (hseparated (a i) (hamem i) (a j) (hamem j)
        (by simpa [f] using h))
    · exact False.elim (hseparated (a j) (hamem j) (a i) (hamem i)
        (by simpa [f] using h.symm))
    · have hij : i = j := ha (τ.injective (by simpa [f] using h))
      cases hij
      rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro j
    simp [f]
  · rintro ⟨j, b⟩
    fin_cases b
    · simpa [f] using (hmarked (a j) (hamem j)).1
    · simpa [f] using (hmarked (a j) (hamem j)).2

end PeriodicTilingThree

end OAI
