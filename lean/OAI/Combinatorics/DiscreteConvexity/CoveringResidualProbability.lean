import OAI.Combinatorics.DiscreteConvexity.CoveringBasic
import OAI.Combinatorics.DiscreteConvexity.Bernoulli

namespace OAI

/-!
# Exact survival probability of a tuple of distinct edges

The sampling coordinates are ordered pairs of edges, not their unions. Every
ordered pair of positions contributes a distinct coordinate, including each
diagonal position. The product Bernoulli law therefore assigns exactly
`(1 - p) ^ (m * m)` to the event that all these coordinates are absent.
-/

namespace TalagrandDiscreteConvexity.Covering

/-- Applying an injection in both coordinates preserves ordered pairs. -/
theorem orderedPairMap_injective {I E : Type*} {e : I → E}
    (he : Function.Injective e) :
    Function.Injective (fun ij : I × I => (e ij.1, e ij.2)) := by
  intro ij kl h
  apply Prod.ext
  · exact he (congrArg Prod.fst h)
  · exact he (congrArg Prod.snd h)

variable {X : Type*} [DecidableEq X]

noncomputable section

/-- The tuple uses all `m * m` ordered pair coordinates, including the diagonal. -/
theorem tuplePairs_card {H : Family X} {m : ℕ} (f : EdgeTuple H m) :
    (tuplePairs f).card = m * m := by
  classical
  rw [tuplePairs, Finset.card_image_of_injective _
    (orderedPairMap_injective f.property)]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- A diagonal edge pair is one of the sampled coordinates used by the tuple. -/
theorem diagonal_mem_tuplePairs {H : Family X} {m : ℕ}
    (f : EdgeTuple H m) (i : Fin m) : (f.val i, f.val i) ∈ tuplePairs f := by
  exact mem_tuplePairs.mpr ⟨i, i, rfl⟩

/-- Avoiding the pair set means that none of the ordered tuple pairs was sampled. -/
theorem disjoint_tuplePairs_iff {H : Family X} {m : ℕ}
    (f : EdgeTuple H m) (sample : Sample H) :
    Disjoint sample (tuplePairs f) ↔ ∀ i j, (f.val i, f.val j) ∉ sample := by
  constructor
  · intro h i j hij
    exact Finset.disjoint_left.mp h hij (mem_tuplePairs.mpr ⟨i, j, rfl⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro pair hsample htuple
    obtain ⟨i, j, rfl⟩ := mem_tuplePairs.mp htuple
    exact h i j hsample

/-- Exact residual probability under the actual finite product Bernoulli law. -/
theorem tuple_survival_probability {H : Family X} {m : ℕ}
    (f : EdgeTuple H m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := ↥H × ↥H) p hp0 hp1).prob
      (fun sample => Disjoint sample (tuplePairs f)) = (1 - p) ^ (m * m) := by
  rw [bernoulliLaw_prob_disjoint, tuplePairs_card]

end
end TalagrandDiscreteConvexity.Covering

end OAI
