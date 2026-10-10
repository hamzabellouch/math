import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges

namespace OAI

/-! The real Liouville test function on ambient integer vertices and
the exact cancellation of the square-root weights on each directed edge. -/

namespace TwoPointCorrelations

open scoped Classical

noncomputable def integerLiouville (n : ℤ) : ℂ := liouville n.toNat

lemma liouville_norm_le_one (n : ℕ) : ‖liouville n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [liouville]
  · exact liouville_oneBounded n (Nat.pos_of_ne_zero hn)

lemma integerLiouville_norm_le_one (n : ℤ) : ‖integerLiouville n‖ ≤ 1 :=
  liouville_norm_le_one _

lemma integerLiouville_natCast (n : ℕ) : integerLiouville n = liouville n := by
  simp [integerLiouville]

lemma star_integerLiouville (n : ℤ) : star (integerLiouville n) = integerLiouville n := by
  simp [integerLiouville, liouville]

lemma directedEdge_liouville_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ)
    (hg : ∀ z, g z ≠ 0) :
    star ((g n : ℂ) * integerLiouville n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q n m : ℂ) *
        ((g m : ℂ) * integerLiouville m) =
      if q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra m then
          (L * u q * center n : ℝ) * integerLiouville n * integerLiouville m else 0 := by
  unfold directedIntegerEdge
  split_ifs with he
  · simp only [star_mul, Complex.star_def, Complex.conj_ofReal, star_integerLiouville,
      Complex.ofReal_div, Complex.ofReal_mul]
    have hn : (g n : ℂ) ≠ 0 := by exact_mod_cast hg n
    have hm : (g m : ℂ) ≠ 0 := by exact_mod_cast hg m
    field_simp
  · simp

end TwoPointCorrelations

end OAI
