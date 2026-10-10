import OAI.NumberTheory.CubicMoment.Estimates.GramMellinTwist
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveDualConjugation

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullSquarefreePrimeSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) : Finset Eisenstein :=
  (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
    (fun b => Squarefree b ∧ IsCoprime b e)

lemma fullSquarefreePrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    primary b ∧ Squarefree b := by
  have hm := Finset.mem_filter.mp hb
  exact ⟨orderedPrimarySupport_primary _ (fun i b hb => (fullPrimeSupport_prime R W X i b hb).1) hm.1,hm.2.1⟩

lemma fullPrimeCoefficient_sum_squarefree (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
      (fun b => IsCoprime b e), fullPrimeCoefficient R W X b*f b) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, fullPrimeCoefficient R W X b*f b := by
  simp only [fullSquarefreePrimeSupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hsf : Squarefree b
  · simp only [hsf,true_and]
  · simp [hsf,fullPrimeCoefficient,squarefreeConvolution]

lemma gramMellinPhase_neg (t x : ℝ) :
    gramMellinPhase (-t) x = star (gramMellinPhase t x) := by
  rw [gramMellinPhase_eq_mellinPhase,gramMellinPhase_eq_mellinPhase,star_mellinPhase]
  congr 1
  ring

theorem fullStructuredPrimeRow_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (fullPrimeCoefficient R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)‖ =
      ‖fullStructuredPrimeSum R h 1 1 e (u+2*Real.pi*t) W X‖ := by
  have he : (∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (fullPrimeCoefficient R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)) =
      star (mellinPhase (-(2*Real.pi*t)) N*
        fullStructuredPrimeSum R h 1 1 e (u+2*Real.pi*t) W X) := by
    calc
      _ = star (∑ b ∈ fullSquarefreePrimeSupport R W X e,
          fullPrimeCoefficient R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [star_mul]
        ring
      _ = star (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
          (fun b => IsCoprime b e), fullPrimeCoefficient R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) :=
        congrArg star (fullPrimeCoefficient_sum_squarefree R W X e _).symm
      _ = _ := by
        congr 1
        convert fullStructuredPrimeSum_gram_twist R h 1 e u t W X hN using 1
        apply Finset.sum_congr rfl
        intro b hb
        simp only [one_mul]
        ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

theorem fullStructuredPrimeRow_reverse_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (fullPrimeCoefficient R W X b*mellinPhase u (norm b))*
        gramMellinPhase t (norm b/N)*star (cubicSymbol b h)‖ =
      ‖fullStructuredPrimeSum R h 1 1 e (u-2*Real.pi*t) W X‖ := by
  have he := fullStructuredPrimeRow_norm R W X h e u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  congr 2
  ring

end CubicFirstMoment

end

end OAI
