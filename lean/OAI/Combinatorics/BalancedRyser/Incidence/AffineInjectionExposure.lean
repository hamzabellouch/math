import OAI.Combinatorics.BalancedRyser.Incidence.AffineDirectionCounting
import OAI.Combinatorics.BalancedRyser.Local.InjectionAuxiliaryExposure
import OAI.Combinatorics.BalancedRyser.Local.InjectionExposure

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

theorem projection_uniform_injection_probability_le
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (p : Point F) (l m : Line F) (hne : l ≠ m) :
    ((PMF.uniformOfFinset (InjectionExposure.completions K base)
      (InjectionExposure.completions_nonempty K base)).toOuterMeasure
        {e | e i ≠ l.1 ∧ lineIntersection l (lineThrough (e i) p) ≠ p ∧
          OnLine (lineIntersection l (lineThrough (e i) p)) m}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.next_event_probability_le K base i hi
    (fun d => d ≠ l.1 ∧ lineIntersection l (lineThrough d p) ≠ p ∧
      OnLine (lineIntersection l (lineThrough d p)) m)
    (card_projection_directions_le_one (InjectionExposure.remaining K base) p l m hne)
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

theorem projection_uniform_injection_probability_le_token_budget
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (p : Point F) (l m : Line F) (hne : l ≠ m)
    (b : ℕ) (hK : K.card ≤ 5 * b) (hb : 5 * b < Fintype.card F + 1) :
    ((PMF.uniformOfFinset (InjectionExposure.completions K base)
      (InjectionExposure.completions_nonempty K base)).toOuterMeasure
        {e | e i ≠ l.1 ∧ lineIntersection l (lineThrough (e i) p) ≠ p ∧
          OnLine (lineIntersection l (lineThrough (e i) p)) m}).toReal ≤
      1 / ((Fintype.card F + 1 - 5 * b : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.next_event_probability_le_budget K base i hi
    (fun d => d ≠ l.1 ∧ lineIntersection l (lineThrough d p) ≠ p ∧
      OnLine (lineIntersection l (lineThrough d p)) m)
    (card_projection_directions_le_one (InjectionExposure.remaining K base) p l m hne)
    (5 * b) hK (by simpa only [Direction, Fintype.card_option] using hb)
  simpa only [Direction, Fintype.card_option] using h

theorem auxiliary_projection_injection_probability_le
    {Z : Type*} [Fintype Z]
    (K : Finset I) (base : I ↪ Direction F) (i : I) (hi : i ∉ K)
    (noise : (I ↪ Direction F) → PMF Z)
    (hnoise : InjectionExposure.DependsOnExposed K noise)
    (p : Z → Point F) (l m : Z → Line F) (hne : ∀ z, l z ≠ m z) :
    ((InjectionExposure.auxiliaryLaw K base noise).toOuterMeasure
      {x | x.1 i ≠ (l x.2).1 ∧
        lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2)) ≠ p x.2 ∧
        OnLine (lineIntersection (l x.2) (lineThrough (x.1 i) (p x.2))) (m x.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  classical
  have h := InjectionExposure.auxiliary_next_event_probability_le K base noise hnoise i hi
    (fun z d => d ≠ (l z).1 ∧ lineIntersection (l z) (lineThrough d (p z)) ≠ p z ∧
      OnLine (lineIntersection (l z) (lineThrough d (p z))) (m z))
    (fun z => card_projection_directions_le_one (InjectionExposure.remaining K base)
      (p z) (l z) (m z) (hne z))
  simpa only [InjectionExposure.card_remaining, Direction, Fintype.card_option] using h

end Balanced

end OAI
