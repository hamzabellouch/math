import OAI.Analysis.Pureness.Divisibility.NuclearTracelessStabilizedComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
  (k+1) • u ≤ k • v → u ≤ v)
variable (htrace : ¬ Nonempty (TracialState A))
include hsimple hA hAU htrace

theorem sharedCuntz_le_nonzero_of_nuclear_no_trace
    (x y : CuntzClass (MatrixLimit A)) (hy : y ≠ 0) : x ≤ y := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  have hb : b.1 ≠ 0 := by
    intro hz
    apply hy
    have hb : b = Positive.zero := Subtype.ext hz
    change CuntzClass.mk b = 0
    rw [hb, CuntzClass.zero_mk]
  exact (cuntzSubequiv_iff_shared a b).mp
    (stabilizedComparison_of_nuclear_no_trace hsimple hA hAU htrace a b hb)

theorem almostDivisible_of_nuclear_no_trace
    (x : CuntzClass (MatrixLimit A)) (n : ℕ) :
    ∃ y : CuntzClass (MatrixLimit A), n • y ≤ x ∧ x ≤ (n+1) • y := by
  refine ⟨x, ?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · exact sharedCuntz_le_nonzero_of_nuclear_no_trace hsimple hA hAU htrace _ x hx
  · rw [add_nsmul, one_nsmul]
    exact le_add_of_nonneg_left (sharedCuntz_zero_le (n • x))
end CuntzPureness

end

end OAI
