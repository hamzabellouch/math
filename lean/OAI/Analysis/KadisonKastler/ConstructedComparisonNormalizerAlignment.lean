import OAI.Analysis.KadisonKastler.ConstructedModularActionCorrection
import OAI.Analysis.KadisonKastler.ModularComparisonGap

namespace OAI

/-! # From comparison normalizers to a common action

Multiplying the selected normalizer of `V(g) U(g)*` by `U(g)` produces
a normalizer close to the actual representation `V`. The choices need
no regularity; the invariant-mean correction supplies one conjugating unitary.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem constructed_norm_comparison_normalizer_error
    (u v n : unitary (H →L[ℂ] H)) :
    ‖((n * u : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - v‖ =
      ‖(n : H →L[ℂ] H) - ((v * star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)‖ := by
  have he : ((n * u : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - v =
      ((n : H →L[ℂ] H) - ((v * star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) * u := by
    simp only [Submonoid.coe_mul, Unitary.coe_star, sub_mul, mul_assoc,
      Unitary.star_mul_self_of_mem u.property, mul_one]
  rw [he, CStarRing.norm_mul_coe_unitary]

theorem constructed_exists_common_action_of_comparison_normalizers
    (M : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization M)
    (m : ScalarInvariantMean G)
    (U V : G →* unitary (H →L[ℂ] H))
    (hU : ∀ g, Conjugates (U g) M M)
    (n : G → unitary (H →L[ℂ] H)) (hn : ∀ g, Conjugates (n g) M M)
    {d : ℝ} (hd : 0 ≤ d) (hsmall : 3 * d ≤ 1 / 16384)
    (hclose : ∀ g,
      ‖(n g : H →L[ℂ] H) - ((V g * star (U g) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)‖ ≤ d) :
    ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ 3074 * d ∧
      ∀ g, Conjugates (V g) (unitaryConjugateAlgebra q M)
        (unitaryConjugateAlgebra q M) := by
  apply constructed_exists_common_action_of_near_normalizers M hpub m V (fun g => n g * U g)
    (fun g => (hU g).trans (hn g)) hd hsmall
  intro g
  rw [constructed_norm_comparison_normalizer_error]
  exact hclose g

end

end KadisonKastler

end OAI
