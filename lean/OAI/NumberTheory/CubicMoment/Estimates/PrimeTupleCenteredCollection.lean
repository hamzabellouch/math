import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleRegrouping
import OAI.NumberTheory.CubicMoment.Estimates.CenteredPrimeKernel
import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows

namespace OAI

/-! Exact collection against the centered kernel. Its vanishing on
nonsquarefree products justifies the separate squarefree convolutions;
mutual coprimality remains in the original centered kernel. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma centered_ordered_to_squarefree (S : ι → Finset Eisenstein)
    (T : κ → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (v : κ → Eisenstein → ℂ)
    (hS : ∀ i a, a ∈ S i → primary a) (hT : ∀ i a, a ∈ T i → primary a) (u : ℝ) :
    (∑ a ∈ orderedConvolutionSupport S, ∑ b ∈ orderedConvolutionSupport T,
      orderedConvolution S w a*orderedConvolution T v b*centeredGauss (a*b)*normTwist u (a*b)) =
      ∑ a ∈ (orderedConvolutionSupport S).filter Squarefree,
        ∑ b ∈ (orderedConvolutionSupport T).filter Squarefree,
          squarefreeConvolution S w a*squarefreeConvolution T v b*
            centeredGauss (a*b)*normTwist u (a*b) := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hpa := orderedPrimarySupport_primary S hS ha
  by_cases hsa : Squarefree a
  · simp only [hsa,ite_true]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hsb : Squarefree b
    · simp only [hsb,ite_true,squarefreeConvolution,hsa]
    · have hn : ¬Squarefree (a*b) := fun h => hsb (h.squarefree_of_dvd (dvd_mul_left b a))
      have hz := centeredGauss_vanishes
        (primary_mul hpa (orderedPrimarySupport_primary T hT hb)) hn
      simp only [hsb,ite_false,hz,mul_zero,zero_mul]
  · simp only [hsa,ite_false]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : ¬Squarefree (a*b) := fun h => hsa (h.squarefree_of_dvd (dvd_mul_right a b))
    rw [centeredGauss_vanishes (primary_mul hpa (orderedPrimarySupport_primary T hT hb)) hn,
      mul_zero,zero_mul]

lemma full_prime_centered_collection (S : ι → Finset Eisenstein)
    (T : κ → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (v : κ → Eisenstein → ℂ)
    (hS : ∀ i a, a ∈ S i → primary a) (hT : ∀ i a, a ∈ T i → primary a) (u : ℝ) :
    (∑ f ∈ Fintype.piFinset S, ∑ g ∈ Fintype.piFinset T,
      (∏ i, w i (f i))*(∏ i, v i (g i))*centeredGauss ((∏ i, f i)*(∏ i, g i))*
        normTwist u ((∏ i, f i)*(∏ i, g i))) =
      ∑ a ∈ (orderedConvolutionSupport S).filter Squarefree,
        ∑ b ∈ (orderedConvolutionSupport T).filter Squarefree,
          squarefreeConvolution S w a*squarefreeConvolution T v b*
            centeredGauss (a*b)*normTwist u (a*b) := by
  rw [←centered_ordered_to_squarefree S T w v hS hT u]
  symm
  calc
    _ = ∑ a ∈ orderedConvolutionSupport S, orderedConvolution S w a*
        ∑ b ∈ orderedConvolutionSupport T,
          orderedConvolution T v b*(centeredGauss (a*b)*normTwist u (a*b)) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro f _hf
      rw [orderedConvolution_sum,Finset.mul_sum]
      simp only [mul_assoc]

lemma full_prime_squarefree_centered_collection (R : ℝ)
    (WA : ι → ℝ → ℂ) (WB : κ → ℝ → ℂ) (XA : ι → ℝ) (XB : κ → ℝ) (u : ℝ) :
    (∑ f ∈ Fintype.piFinset (fullPrimeSupport R WA XA),
      ∑ g ∈ Fintype.piFinset (fullPrimeSupport R WB XB),
        (∏ i, WA i (norm (f i)/XA i))*(∏ i, WB i (norm (g i)/XB i))*
          centeredGauss ((∏ i, f i)*(∏ i, g i))*normTwist u ((∏ i, f i)*(∏ i, g i))) =
      ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
        ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
          fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
            centeredGauss (a*b)*normTwist u (a*b) := by
  simpa only [fullSquarefreePrimeSupport,isCoprime_one_right,and_true,fullPrimeCoefficient] using
    full_prime_centered_collection (fullPrimeSupport R WA XA) (fullPrimeSupport R WB XB)
      (fun i p => WA i (norm p/XA i)) (fun i p => WB i (norm p/XB i))
      (fun i p hp => (fullPrimeSupport_prime R WA XA i p hp).1)
      (fun i p hp => (fullPrimeSupport_prime R WB XB i p hp).1) u

end CubicFirstMoment

end

end OAI
