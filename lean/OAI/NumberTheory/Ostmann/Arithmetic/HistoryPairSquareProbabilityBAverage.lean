import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityBAverageCRT

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCRTIntegration HistorySignedResidueFactorization ResidueHaar
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem unit_B_average_kernel_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r))))
    [NeZero (representativeModulus h k)] :
    0 ≤ (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r)-
      (average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))).re ∧
    (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r)-
      (average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))).re ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r) := by
  rw [unit_B_average_eq_product h k hs ks had,← Complex.ofReal_prod,Complex.ofReal_re]
  exact actual_unit_square_product_loss h k hs ks hroot hx

theorem mixed_B_average_kernel_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r))))
    [NeZero (representativeModulus h k)] :
    0 ≤ (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r)-
      (average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))).re ∧
    (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r)-
      (average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))).re ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r) := by
  rw [mixed_B_average_eq_product h k hs ks had,← Complex.ofReal_prod,Complex.ofReal_re]
  exact actual_mixed_square_product_loss h k hs ks hroot hx

theorem unit_B_average_kernel_error (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r))))
    [NeZero (representativeModulus h k)] :
    ‖average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))-
      ((∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r):ℝ)‖ ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r) := by
  have hh := actual_unit_square_product_loss h k hs ks hroot hx
  rw [unit_B_average_eq_product h k hs ks had,← Complex.ofReal_prod,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith :
    (∏r : Representative h k,actualUnitSquareProbability h k hs ks r)-
      (∏r : Representative h k,HistoryPairPolynomialKernel.unitKernel h k hs ks r) ≤ 0)]
  linarith

theorem mixed_B_average_kernel_error (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hroot : RootGiantsAgree h k)
    (hx : ∀r : Representative h k,HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r))))
    [NeZero (representativeModulus h k)] :
    ‖average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))-
      ((∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r):ℝ)‖ ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r) := by
  have hh := actual_mixed_square_product_loss h k hs ks hroot hx
  rw [mixed_B_average_eq_product h k hs ks had,← Complex.ofReal_prod,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith :
    (∏r : Representative h k,actualMixedSquareProbability h k hs ks r)-
      (∏r : Representative h k,HistoryPairPolynomialKernel.mixedKernel h k hs ks r) ≤ 0)]
  linarith

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
