import OAI.MeasureTheory.Falconer.Recursion.SourceClassContact
import OAI.MeasureTheory.Falconer.Recursion.UniformContactDepths
import OAI.MeasureTheory.Falconer.Recursion.RoundedContactWidth

namespace OAI

/-! # Actual integer-depth three-interval data for each retained source class -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped NNReal
variable {d : ℕ}

theorem source_class_contact_intervals (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {q t τ γ : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (hγ : 0 < γ)
    (hlarge : 4 ≤ γ*(N:ℝ))
    (hcontact : RobustProfileContact (sourceUnitProfile Q μ N B p) q t τ γ) :
    ∃ A B' : ℝ, ∃ a b : ℕ,
      γ ≤ B'-A ∧ B'-A ≤ 1 ∧ a ≤ b ∧ b ≤ N ∧
      (B'-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B'-A)*(N:ℝ)+1 ∧
      (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧ (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧
      γ*(N:ℝ) ≤ (N-b:ℕ) ∧ (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) ∧
      (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-τ*(B'-A) ≤ sourceProfile Q μ N B p j) ∧
      (∀ j : ℕ, a ≤ j → j ≤ b →
        t*(j-a:ℕ)/N-τ*(B'-A)-((d:ℝ)+t)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p a) ∧
      (∀ j : ℕ, b ≤ j → j ≤ N →
        q*(j-b:ℕ)/N-τ*(B'-A)-((d:ℝ)+q)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p b) := by
  obtain ⟨A,B',hA,hAB,hB',hBA,hfirst,hmiddle,hlast⟩ := hcontact
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hAB' : A ≤ B' := by linarith
  have hB1 : B' ≤ 1 := by linarith
  have hround := rounded_profile_contact
    (sourceUnitProfile_properties Q μ hN hB p).2.2.2.1 hA0 hAB' hB1 hq ht
    hfirst hmiddle hlast hN
  have hdepth := uniform_contact_depth_bounds hγ hA hAB hB' hBA hN hlarge
  have hgap := rounded_contact_width hA0 hAB' N
  refine ⟨A,B',Nat.floor (A*(N:ℝ)),Nat.floor (B'*(N:ℝ)),by linarith,by linarith,
    hdepth.1,hdepth.2.1,hgap.1,hgap.2,hdepth.2.2.1,hdepth.2.2.2.1,
    hdepth.2.2.2.2.1,hdepth.2.2.2.2.2,?_⟩
  simpa only [sourceUnitProfile_at_depth Q μ hN B p,NNReal.coe_natCast] using hround

end Falconer.Regularization

end OAI
