import OAI.Algebra.DepthFive.IsolatedWeight
import OAI.Algebra.DepthFive.WordSwitches

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.PathIsolatedWeight

/-- Adjacent positions of the path, in either orientation. -/
def adjacent {n : ℕ} (i j : Fin (n + 1)) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- Interior selected positions are exactly those eligible for the two-switch flip. -/
def interior {n : ℕ} (V : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  V.filter fun i => 0 < i.val ∧ i.val < n

theorem interior_subset {n : ℕ} (V : Finset (Fin (n + 1))) : interior V ⊆ V :=
  Finset.filter_subset _ _

theorem pathEdges_adjacent (n : ℕ) :
    ∀ e ∈ SwitchRestoration.pathEdges n, adjacent e.1 e.2 ∧ adjacent e.2 e.1 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  constructor
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem independent_of_no_adjacent {n : ℕ} (V : Finset (Fin (n + 1)))
    (hV : ∀ i : Fin n, ¬ (i.castSucc ∈ V ∧ i.succ ∈ V)) :
    ∀ i ∈ V, ∀ j, adjacent i j → j ∉ V := by
  intro i hi j hij hj
  rcases hij with hij | hji
  · let t : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have ht : t.castSucc = i := by apply Fin.ext; rfl
    have ht' : t.succ = j := by apply Fin.ext; exact hij
    exact hV t ⟨ht.symm ▸ hi, ht'.symm ▸ hj⟩
  · let t : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have ht : t.castSucc = j := by apply Fin.ext; rfl
    have ht' : t.succ = i := by apply Fin.ext; exact hji
    exact hV t ⟨ht.symm ▸ hj, ht'.symm ▸ hi⟩

theorem endpointDegree_interior {n : ℕ} (V : Finset (Fin (n + 1))) :
    ∀ i ∈ interior V, SwitchRestoration.endpointDegree (SwitchRestoration.pathEdges n) i = 2 := by
  intro i hi
  exact SwitchRestoration.endpointDegree_pathEdges_interior i
    (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2

theorem exceptional_subset_first {n : ℕ} (V : Finset (Fin (n + 1)))
    (hlast : Fin.last n ∉ V) : V \ interior V ⊆ {0} := by
  intro i hi
  obtain ⟨hiV, hiS⟩ := Finset.mem_sdiff.mp hi
  have hn : i.val ≠ n := by
    intro h
    have he : i = Fin.last n := Fin.ext h
    exact hlast (he ▸ hiV)
  have hz : i.val = 0 := by
    by_contra h
    apply hiS
    exact Finset.mem_filter.mpr ⟨hiV, by have := i.isLt; omega⟩
  simp only [Finset.mem_singleton]
  exact Fin.ext hz

theorem exceptional_card_le_one {n : ℕ} (V : Finset (Fin (n + 1)))
    (hlast : Fin.last n ∉ V) : (V \ interior V).card ≤ 1 := by
  simpa using Finset.card_le_card (exceptional_subset_first V hlast)

theorem switchCount_eq_wordSwitches {n : ℕ} (w : Fin (n + 1) → Bool) :
    SwitchRestoration.switchCount (SwitchRestoration.pathEdges n) w =
      (WordSwitches.switches w).card := by
  rw [SwitchRestoration.switchCount_pathEdges]
  simp only [WordSwitches.switches, Finset.card_filter]

/-- Correction removal for the concrete path: all graph hypotheses are discharged. -/
theorem sum_weight_le_uniform {n : ℕ} (V : Finset (Fin (n + 1)))
    (hV : ∀ i : Fin n, ¬ (i.castSucc ∈ V ∧ i.succ ∈ V))
    (hlast : Fin.last n ∉ V)
    {A B x : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ w : Fin (n + 1) → Bool,
      IsolatedWeight.weight (SwitchRestoration.pathEdges n) V adjacent A B x w) ≤
      (1 + 2 * x ^ 2) ^ V.card * (1 + A) * (1 + A * x) ^ V.card *
        ∑ w : Fin (n + 1) → Bool,
          IsolatedWeight.baseWeight (SwitchRestoration.pathEdges n) V A B x w := by
  exact IsolatedWeight.sum_weight_le_uniform_uncorrected
    (interior_subset V) (independent_of_no_adjacent V hV) (pathEdges_adjacent n)
    (endpointDegree_interior V) (exceptional_card_le_one V hlast) hA hB hx hx1

end Problem335.PathIsolatedWeight

end

end OAI
