import OAI.Combinatorics.Crossing.AxisConcurrency

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def AxisIndependentTriple (e f g : BipartiteEdge m n) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ g.1 ∧ f.1 ≠ g.1 ∧ e.2 ≠ f.2 ∧ e.2 ≠ g.2 ∧ f.2 ≠ g.2

theorem exists_axis_generic_positions (lo hi : BipartiteVertex m n → ℝ)
    (hinterval : ∀ j, lo j < hi j) :
    ∃ x : BipartiteVertex m n → ℝ, (∀ j, x j ∈ Set.Ioo (lo j) (hi j)) ∧
      ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
        axisConcurrency (x (Sum.inl e.1)) (x (Sum.inr e.2)) (x (Sum.inl f.1)) (x (Sum.inr f.2))
          (x (Sum.inl g.1)) (x (Sum.inr g.2)) ≠ 0 := by
  classical
  let P : (BipartiteEdge m n × BipartiteEdge m n × BipartiteEdge m n) → MvPolynomial (BipartiteVertex m n) ℝ :=
    fun t => if AxisIndependentTriple t.1 t.2.1 t.2.2 then axisConcurrencyPolynomial t.1 t.2.1 t.2.2 else 1
  have hP : ∀ t, P t ≠ 0 := by
    intro t
    dsimp only [P]
    split_ifs with h
    · exact axisConcurrencyPolynomial_ne_zero _ _ _ h.1 (Ne.symm h.2.2.1)
        (Ne.symm h.2.2.2.1) (Ne.symm h.2.2.2.2.1)
    · exact one_ne_zero
  obtain ⟨x,hx,havoid⟩ := exists_box_avoiding_polynomials P hP lo hi hinterval
  refine ⟨x,hx,?_⟩
  intro e f g htriple
  have hh := havoid (e,f,g)
  simpa only [P,ite_eq_left htriple,axisConcurrencyPolynomial_eval] using hh

end Zarankiewicz

end

end OAI
