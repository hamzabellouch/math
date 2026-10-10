import OAI.Analysis.Pureness.Cuntz.SemigroupStateSeparation
import OAI.Analysis.Pureness.Cuntz.FiniteCuntzFullness

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteCuntz_le_of_states (hsimple : TopologicallySimple A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0)
    (x : finiteCuntzSubmonoid (A := A))
    (hgap : ∀ f : StateSpace y, f.1 x < 1) : x ≤ y :=
  le_of_states finiteCuntz_zero_le (finiteCuntz_almostUnperforated hAU) y x
    (finiteCuntz_nonzero_orderUnit hsimple y hy) hgap

theorem finiteComparison_of_states (hsimple : TopologicallySimple A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (L : ℕ) (M N : Positive (FinMatrix A L)) (hN : N.1 ≠ 0)
    (hgap : ∀ f : StateSpace (finitePositiveClass L N), f.1 (finitePositiveClass L M) < 1) :
    CuntzSubequiv M.1 N.1 := by
  apply (finitePositiveClass_le_iff L M N).mp
  exact finiteCuntz_le_of_states hsimple hAU _
    (fun h => hN ((finitePositiveClass_eq_zero_iff L N).mp h)) _ hgap

theorem finiteCuntz_le_of_no_states (hsimple : TopologicallySimple A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0)
    (hstates : IsEmpty (StateSpace y)) (x : finiteCuntzSubmonoid (A := A)) : x ≤ y := by
  exact finiteCuntz_le_of_states hsimple hAU y hy x (fun f => (hstates.false f).elim)

theorem finiteCuntz_no_states_iff_properlyInfinite (hsimple : TopologicallySimple A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) :
    IsEmpty (StateSpace y) ↔ 2 • y ≤ y :=
  ⟨fun h => finiteCuntz_le_of_no_states hsimple hAU y hy h _,
    no_state_of_properlyInfinite y⟩
end CuntzPureness

end

end OAI
