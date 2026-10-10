import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedMatchedRelabel

namespace OAI

/-! # Constants in the original matched-history exterior factor -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedKernel_mul {σ I B : Type*} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (bulk : Bool → TreeLeafTuple (List B) n)
    (weight : (B → σ) → ℂ) (W : (B → σ) → ℝ → ℝ → ℂ)
    (u v r w center : ℝ) (y : B → σ)
    (a : MovingSampleSlots σ n × MovingSampleSlots σ n) :
    movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S ψ X lo hi φ G
      t small bulk (fun y x z => weight y * W y x z) u v r w center y a =
    weight y * movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S
      ψ X lo hi φ G t small bulk W u v r w center y a := by
  unfold movingWeightedMatchedKernel
  simp_rw [mul_left_comm _ (weight y), complexIntegerInterval_const_mul,
    complexPrimeInterval_const_mul]

end Ostmann

end OAI
