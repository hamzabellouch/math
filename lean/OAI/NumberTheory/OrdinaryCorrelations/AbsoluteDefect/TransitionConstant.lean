import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinnedStage
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MomentCoefficient
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CrossTransitionEnergy
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EvenLengthLower
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AnalyticTransition

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryTwoScaleCofactor OrdinaryFrequencyChain Finset
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

noncomputable def transitionConstant : ℝ := 24*Real.exp (1+1/4)*gaussianConstant

lemma transitionConstant_nonneg : 0≤ transitionConstant := by
  unfold transitionConstant gaussianConstant
  positivity

theorem actual_next_stage {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {B H s j K X : ℕ}
    (hA : transitionConstant+Real.exp 1+10≤(2:ℝ)^K)
    (hB : H+4*s+K+70≤B) (hB' : 2*H+s+30≤B)
    (hX : 2*2^(F B s (j+1))≤X)
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤(X:ℝ)) :
    (∑t∈firstGood S
      (allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
        (fun _stage i=>primeMellin f χ (primeBin i))
        (fun j i=>threshold H j (binLog B H s j i))) (j+1),
      ‖binnedStage f χ (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)) X t‖^2)
      ≤Real.exp (-993*(mesh B H s (j+1):ℝ)) := by
  have hB0 : H+10≤B := by omega
  have hXp : 0<X := lt_of_lt_of_le (by positivity : 0<2*2^(F B s (j+1))) hX
  let I := fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j)
  let Q := fun (_ : ℕ) i=>primeMellin f χ (primeBin i)
  let C := fun j i=>dyadicCofactorMellin f χ
    (primeWindow (binQ B H s j) (binStart B H s j) (binWidth B s j)) (evenBinLength X i)
  let V := fun j i=>threshold H j (binLog B H s j i)
  have hn := next_stage_energy S I Q C V j
  apply hn.trans
  apply le_trans ?_ (transition_total transitionConstant_nonneg hA hB hB')
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro a ha
  have hN := grid_lower_pos _ _ _ (by unfold binQ; positivity) ha
  have hu : 0<upper i := (grid_lower_pos _ _ _ (by unfold binQ; positivity) hi).trans_le (lower_le_upper i)
  have hiU := upper_le_endpoint _ _ _ hi
  rw [(window_endpoints B H s (j+1) hB0).2] at hiU
  have hM := even_bin_length_pos (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)) X (by unfold binQ; positivity)
    (by rwa [(window_endpoints B H s (j+1) hB0).2]) hi
  have hh := amplifier_height (B:=B) (H:=H) (s:=s) hB0 hX ha hi
  have hh' : (X:ℝ)+1≤(2*(lower a:ℝ))^(amplifier (binLog B H s j a) (binLog B H s (j+1) i))*(evenBinLength X i:ℝ) := by
    exact_mod_cast (show X+1≤(2*lower a)^(amplifier (binLog B H s j a) (binLog B H s (j+1) i))*evenBinLength X i from (by omega))
  exact dyadic_cross_transition hf χ (primeBin a) (primeBin i)
    (primeWindow (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)))
    (fun p hp => (mem_filter.mp hp).2)
    (amplifier (binLog B H s j a) (binLog B H s (j+1) i)) hN hM
    (bin_dyadic (by unfold binQ; positivity) ha) S (Nat.cast_nonneg _)
    (threshold_pos _ _ _) (threshold_pos _ _ _).le hh'
    (fun t ht => abs_le.mp (hheight t ht)) (fun t ht u hu hne=>hsep ht hu hne)

end OrdinaryChainScales

end

end OAI
