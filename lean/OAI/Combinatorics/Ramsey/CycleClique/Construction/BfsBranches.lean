import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsParent

namespace OAI

/-! The first common ancestor of a set in one distance layer determines two branches. -/

namespace CycleClique.Construction
theorem exists_bfs_branch_partition {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d : ℕ}
    (hY : 2 ≤ Y.card)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d) :
    ∃ p, 1 ≤ p ∧ p ≤ d ∧ ∃ c, ∃ χ : Y → Fin 2,
      (∃ u v, χ u ≠ χ v) ∧
      (∀ v : Y, (bfsParent G root)^[p] v.val = c) ∧
      (∀ u v : Y, χ u ≠ χ v → ∀ j < p,
        (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val) := by
  classical
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
  let P := bfsParent G root
  have hroot : ∀ v ∈ Y, P^[d] v = root := by
    intro v hv
    have h := bfsAncestor_root (hlayer v hv).1
    simpa only [(hlayer v hv).2] using h
  have hex : ∃ p, p ≤ d ∧ ∀ v ∈ Y, P^[p] v = P^[p] v₀ :=
    ⟨d, le_rfl, fun v hv => (hroot v hv).trans (hroot v₀ hv₀).symm⟩
  let p := Nat.find hex
  have hp := Nat.find_spec hex
  change p ≤ d ∧ ∀ v ∈ Y, P^[p] v = P^[p] v₀ at hp
  have hpos : 1 ≤ p := by
    by_contra hn
    have hpzero : p = 0 := by omega
    have hone : Y.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      have h₁ := hp.2 a ha
      have h₂ := hp.2 b hb
      simp only [hpzero, Function.iterate_zero, id_eq] at h₁ h₂
      exact h₁.trans h₂.symm)
    omega
  have hnot : ¬ ∀ v ∈ Y, P^[p - 1] v = P^[p - 1] v₀ := by
    intro hsame
    have hmin := Nat.find_min hex (show p - 1 < Nat.find hex by change p - 1 < p; omega)
    exact hmin ⟨by omega, hsame⟩
  push Not at hnot
  obtain ⟨v₁, hv₁, hdiff⟩ := hnot
  let χ : Y → Fin 2 := fun v => if P^[p - 1] v.val = P^[p - 1] v₀ then 0 else 1
  have hnonconstant : ∃ u v, χ u ≠ χ v := by
    refine ⟨⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩, ?_⟩
    simp [χ, hdiff]
  refine ⟨p, hpos, hp.1, P^[p] v₀, χ, hnonconstant,
    fun v => hp.2 v.val v.property, ?_⟩
  intro u v hχ j hj heq
  have hchild : P^[p - 1] u.val = P^[p - 1] v.val := by
    have h := congrArg (P^[p - 1 - j]) heq
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h
    have hindex : p - 1 - j + j = p - 1 := by omega
    simpa only [hindex] using h
  apply hχ
  dsimp [χ]
  rw [hchild]

end CycleClique.Construction

end OAI
