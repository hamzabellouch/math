import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.TriplePermutation

private lemma pair_symm (x y : E3) : invDistance x y = invDistance y x := by
  simp only [invDistance, norm_sub_rev]

lemma cost_swap_first (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (y, (x, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm y x]
  ac_rfl

lemma cost_swap_last (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (x, (z, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm z y]
  ac_rfl

lemma cost_rotate (x y z : E3) :
    coulombCost (x, (y, z)) = coulombCost (z, (x, y)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd]
  rw [pair_symm z x, pair_symm z y]
  ac_rfl

private lemma cost_eq_of_same_first {x y z b c : E3}
    (h : List.Perm [x, y, z] [x, b, c]) :
    coulombCost (x, (y, z)) = coulombCost (x, (b, c)) := by
  have hp := List.perm_pair.mp (List.Perm.cons_inv h)
  simp only [List.cons.injEq, and_true] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact cost_swap_last _ _ _

/-- The extended Coulomb cost is invariant under every permutation, including
triples with coincident points and infinite cost. -/
lemma cost_eq_of_perm {x y z a b c : E3}
    (h : List.Perm [x, y, z] [a, b, c]) :
    coulombCost (x, (y, z)) = coulombCost (a, (b, c)) := by
  have ha : a ∈ [x, y, z] := h.mem_iff.mpr (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | ha | ha
  · subst a
    exact cost_eq_of_same_first h
  · subst a
    have hs : List.Perm [y, x, z] [x, y, z] := List.Perm.swap x y [z]
    exact (cost_swap_first x y z).trans (cost_eq_of_same_first (hs.trans h))
  · subst a
    have hs : List.Perm [z, x, y] [x, y, z] := by
      simpa using (show List.Perm ([z] ++ [x, y]) ([x, y] ++ [z]) from List.perm_append_comm)
    exact (cost_rotate x y z).trans (cost_eq_of_same_first (hs.trans h))

/-- A common signed potential sum is invariant under the same permutation. -/
lemma real_sum_eq_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    u x + u y + u z = u a + u b + u c := by
  have hs := (h.map u).sum_eq
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc] using hs

/-- The same invariance is available after shifting to a nonnegative potential. -/
lemma ennreal_sum_eq_of_perm {x y z a b c : E3} (u : E3 → ℝ≥0∞)
    (h : List.Perm [x, y, z] [a, b, c]) :
    u x + u y + u z = u a + u b + u c := by
  have hs := (h.map u).sum_eq
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc] using hs

/-- An ordered supporting certificate can be transported to any of its six orders. -/
lemma certificate_iff_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    (ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z))) ↔
      ENNReal.ofReal (u a + u b + u c) ≤ coulombCost (a, (b, c)) := by
  rw [real_sum_eq_of_perm u h, cost_eq_of_perm h]

/-- The equality relation is transported at the same time as the inequality. -/
lemma contact_iff_of_perm {x y z a b c : E3} (u : E3 → ℝ)
    (h : List.Perm [x, y, z] [a, b, c]) :
    (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z))) ↔
      ENNReal.ofReal (u a + u b + u c) = coulombCost (a, (b, c)) := by
  rw [real_sum_eq_of_perm u h, cost_eq_of_perm h]

end Problem356.TriplePermutation

end

end OAI
