import OAI.Combinatorics.Sensitivity.Or

namespace OAI

/-! The two explicit accepting-input cases for an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype I] [Fintype K]

theorem sensitivityAt_orCopies_eq_zero_of_two (f : (I → Bool) → Bool)
    (x : K × I → Bool) {i j : K} (hij : i ≠ j)
    (hi : f (fun a => x (i, a)) = true) (hj : f (fun a => x (j, a)) = true) :
    sensitivityAt (orCopies f) x = 0 := by
  apply (sensitivityAt_eq_zero_iff _ _).mpr
  rintro ⟨k, a⟩
  by_contra h
  have ho := ((compose_flip_sensitive_iff orBits f x k a).mp h).2
  by_cases hk : k = i
  · subst k
    exact ho (orBits_flip_of_witness _ (Ne.symm hij) hj)
  · exact ho (orBits_flip_of_witness _ (Ne.symm hk) hi)

theorem sensitivityAt_orCopies_eq_of_unique (f : (I → Bool) → Bool)
    (x : K × I → Bool) (i : K) (hi : f (fun a => x (i, a)) = true)
    (hother : ∀ j, j ≠ i → f (fun a => x (j, a)) = false) :
    sensitivityAt (orCopies f) x = sensitivityAt f (fun a => x (i, a)) := by
  let y : K → Bool := fun k => f (fun a => x (k, a))
  have hy : orBits y = true := (orBits_eq_true _).mpr ⟨i, hi⟩
  have hf : orBits (flip y {i}) = false := by
    apply (orBits_eq_false _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp [y, hi]
    · rw [flip_singleton_other y hji]
      exact hother j hji
  have hs : (Finset.univ.filter fun k => orBits (flip y {k}) ≠ orBits y) = {i} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hki
      exact hk (orBits_flip_of_witness y (Ne.symm hki) hi)
    · rintro rfl
      rw [hf, hy]
      decide
  change sensitivityAt (compose orBits f) x = _
  rw [sensitivityAt_compose]
  change (∑ k ∈ Finset.univ.filter (fun k => orBits (flip y {k}) ≠ orBits y),
    sensitivityAt f (fun a => x (k, a))) = _
  rw [hs]
  simp

end Paper320

end

end OAI
