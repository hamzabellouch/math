import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingPrimeBound
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open TemplateSupportRemoval Preliminaries Template.OneSidedPhase TemplateOneSidedNumericInputs
attribute [local instance] Classical.propDecidable
variable {I : Type*} [DecidableEq I] {A : ℕ}

def heldPrimeCoordinates (p : I → PrimeUpTo A) (i l : I) (r : PrimeUpTo A) : Other i → ℤ :=
  fun z=>if z.val=l then (r.val:ℤ) else ((p z.val).val:ℤ)

theorem insert_heldPrimeCoordinates (p : I → PrimeUpTo A) (i l : I) (hil : i≠l)
    (q r : PrimeUpTo A) :
    insertCoordinate i (heldPrimeCoordinates p i l r) (q.val:ℤ) =
      fun z=>((twoPrimeSample p i l q r z).val:ℤ) := by
  funext z
  by_cases hz : z=i
  · subst z
    simp only [insertCoordinate_self,twoPrimeSample,Function.update_of_ne hil,Function.update_self]
  · by_cases hzl : z=l
    · subst z
      simp [insertCoordinate,heldPrimeCoordinates,hz,twoPrimeSample]
    · simp [insertCoordinate,heldPrimeCoordinates,hz,hzl,twoPrimeSample]

theorem heldPrimeCoordinates_height (p : I → PrimeUpTo A) (i l : I) (q r : PrimeUpTo A)
    {C z β L : ℝ} (hC : 0 ≤ C)
    (hp : ∀v,Real.log (p v).val ≤ Real.exp (β*L))
    (hq : Real.log q.val ≤ Real.exp (β*L))
    (hr : Real.log r.val ≤ Real.exp (β*L)) :
    ∀v,|((insertCoordinate i (heldPrimeCoordinates p i l r) (q.val:ℤ) v:ℤ):ℝ)| ≤
      Real.exp (rowLogHeight C z β L) := by
  intro v
  by_cases hvi : v=i
  · subst v
    simpa only [insertCoordinate_self,Int.cast_natCast] using source_prime_height C z β L hC q hq
  · by_cases hvl : v=l
    · simp only [insertCoordinate,dite_eq_right hvi,heldPrimeCoordinates,hvl,ite_true,Int.cast_natCast]
      exact source_prime_height C z β L hC r hr
    · simp only [insertCoordinate,dite_eq_right hvi,heldPrimeCoordinates,hvl,ite_false,Int.cast_natCast]
      exact source_prime_height C z β L hC (p v) (hp v)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
