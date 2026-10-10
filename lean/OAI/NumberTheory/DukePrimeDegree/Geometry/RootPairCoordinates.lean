import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerWeights

namespace OAI

/-!
# Coordinates for an arbitrary opposite-root pair

Any two distinct coordinates can be placed first, with a nonempty
complement when the degree is at least three. This removes the coordinate
choice from the centralizer-orbit exclusion.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_rootPair_coordinates {n : ℕ} (hn : 2 < n)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ m : ℕ, 0 < m ∧ ∃ e : Fin n ≃ Fin 2 ⊕ Fin m,
      e.symm (Sum.inl 0) = i ∧ e.symm (Sum.inl 1) = j := by
  let f : Fin 2 → Fin n := ![i, j]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [f, hij, hij.symm] at *
  let C := (Set.range f)ᶜ
  let e₀ : Fin 2 ⊕ C ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl C)).trans
      (Equiv.Set.sumCompl (Set.range f))
  let e : Fin n ≃ Fin 2 ⊕ Fin (Fintype.card C) :=
    e₀.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 2)) (Fintype.equivFin C))
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  have hk : k ∈ C := by
    rintro ⟨a, ha⟩
    fin_cases a
    · exact hki (by simpa [f] using ha.symm)
    · exact hkj (by simpa [f] using ha.symm)
  have hm : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨⟨k, hk⟩⟩
  refine ⟨Fintype.card C, hm, e, ?_, ?_⟩
  · change f 0 = i
    rfl
  · change f 1 = j
    rfl

/-- The centralizer-orbit exclusion for any pair of distinct coordinates,
with no coordinate or weight choices remaining in the assumptions. -/
theorem no_neutral_invariant_rootPair_orbit {n : ℕ} (hn : 2 < n)
    {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : ∀ (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0), ell i = ell j →
      μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) : False := by
  obtain ⟨m, hm, e, hi, hj⟩ := exists_rootPair_coordinates hn i j hij
  subst i
  subst j
  exact no_invariant_rootPair_orbit e hm hij μ x hfull hinv

end DukePrimeDegree

end

end OAI
