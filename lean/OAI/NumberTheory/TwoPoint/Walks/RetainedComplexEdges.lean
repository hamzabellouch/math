import OAI.NumberTheory.TwoPoint.Walks.RetainedLiouvilleEdges

namespace OAI

/-! The retained real edge kernel tested against two arbitrary complex functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedComplexScalar (g : ℤ → ℝ) (keep : ℤ → Prop)
    (f : ℤ → ℂ) (n : ℤ) : ℂ := if keep n then (g n : ℂ) * f n else 0

noncomputable def retainedRealEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra keep : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℝ :=
  if keep n ∧ keep m ∧ q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧
    eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n ∧
    integerEdgeKeep Q u eligible g L K extra m then L * u q * center n else 0

lemma retainedRealEdge_support (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hm : m ≠ n + (h * q * d : ℕ)) :
    retainedRealEdge Q u eligible g center L K extra keep h d q n m = 0 := by
  unfold retainedRealEdge
  split_ifs with he
  · exact (hm he.2.2.2.1).elim
  · rfl

theorem retainedRealEdge_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hg : ∀ z, g z ≠ 0) (F G : ℤ → ℂ) :
    star (retainedComplexScalar g keep (fun z => star (F z)) n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q n m : ℂ) *
        retainedComplexScalar g keep G m =
      F n * G m * (retainedRealEdge Q u eligible g center L K extra keep h d q n m : ℂ) := by
  by_cases hn : keep n
  · by_cases hm : keep m
    · simp only [retainedComplexScalar, retainedRealEdge, hn, hm, ite_true, true_and]
      unfold directedIntegerEdge
      split_ifs
      · have hgn : (g n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hg n)
        have hgm : (g m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hg m)
        simp only [star_mul, star_star]
        have hstar : star (g n : ℂ) = (g n : ℂ) := by simp
        rw [hstar]
        push_cast
        field_simp
      · simp
    · simp [retainedComplexScalar, retainedRealEdge, hm]
  · simp [retainedComplexScalar, retainedRealEdge, hn]

end TwoPointCorrelations

end OAI
