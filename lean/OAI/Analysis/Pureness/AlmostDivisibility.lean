import OAI.Analysis.Pureness.Divisibility.NuclearAlmostDivisibility

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem manuscript_main [TopologicalSpace.SeparableSpace A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hA : IsNuclear.{u,0} A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (x : CuntzClass (MatrixLimit A)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : CuntzClass (MatrixLimit A), n • y ≤ x ∧ x ≤ (n+1) • y := by
  have : Nontrivial A := by
    by_contra h
    have : Subsingleton A := not_nontrivial_iff_subsingleton.mp h
    exact hinf inferInstance
  exact almostDivisible_of_simple_infinite_nuclear hsimple hinf hA hAU x n hn
end CuntzPureness

end

end OAI
