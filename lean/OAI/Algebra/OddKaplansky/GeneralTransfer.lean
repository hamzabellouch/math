import OAI.Algebra.OddKaplansky.Main

namespace OAI

section
namespace OddKaplansky
noncomputable section
open scoped Classical

theorem fixed_field_transfer_general (K L : Type) [Field K] [Group L]
    (M : ℕ) (hM : 2≤M) {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hc : (M : K)≠0)
    (r : ℕ) (_hr : 0<r) (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) :
    ∃ q : ℕ, (r≤M^q ∧ ∀ q'<q, M^q'<r) ∧
      ∃ (Λ : Type) (_ : Group Λ) (_ : Fintype Λ),
        Fintype.card Λ=M*(M^q)^2 ∧
          ∃ a b : MonoidAlgebra K (L×Λ), a*b=1 ∧ b*a≠1 := by
  let : NeZero M := ⟨by omega⟩
  let q := FixedField.leastQ M hM r
  refine ⟨q,⟨FixedField.leastQ_spec M hM r,?_⟩,
    Heisenberg.GroupData M q,inferInstance,inferInstance,Heisenberg.card M q,
    FixedField.output M hM r hζ A,FixedField.output M hM r hζ B,?_⟩
  · intro q' hq'
    by_contra hn
    have hh := FixedField.leastQ_min M hM r (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge hh) hq'
  · exact FixedField.output_products M hM r hζ hc A B hAB hBA
end
end OddKaplansky

end

end OAI
