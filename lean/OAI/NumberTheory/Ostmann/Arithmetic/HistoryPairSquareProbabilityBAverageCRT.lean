import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityBAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCRTIntegration HistorySignedResidueFactorization ResidueHaar
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem unit_B_average_eq_product_of_coprime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hc : Pairwise (fun r t : Representative h k => ((prime h k r)^2).Coprime ((prime h k t)^2)))
    [NeZero (representativeModulus h k)] :
    average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      ((∏r : Representative h k,actualUnitSquareProbability h k hs ks r):ℂ) := by
  let := representativeSquaresNeZero h k hs ks
  have he : (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      (fun z => ∏r : Representative h k,actualUnitSquareIndicator h k hs ks r
        (unitPairEquiv (fun r : Representative h k => (prime h k r)^2) hc z r)) := by
    funext z
    rw [primeResidueIndicatorB_eq_projected_product]
    apply Finset.prod_congr rfl
    intro r _
    simp only [actualUnitSquareIndicator,representativeSquareProjectionB]
    erw [unitPairEquiv_fst_coe,unitPairEquiv_snd_coe]
    rfl
  rw [he]
  erw [unit_product_average]
  simp only [actualUnitSquareIndicator_average]

theorem mixed_B_average_eq_product_of_coprime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hc : Pairwise (fun r t : Representative h k => ((prime h k r)^2).Coprime ((prime h k t)^2)))
    [NeZero (representativeModulus h k)] :
    average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      ((∏r : Representative h k,actualMixedSquareProbability h k hs ks r):ℂ) := by
  let := representativeSquaresNeZero h k hs ks
  have he : (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      (fun z => ∏r : Representative h k,actualMixedSquareIndicator h k hs ks r
        (mixedPairEquiv (fun r : Representative h k => (prime h k r)^2) hc z r)) := by
    funext z
    rw [primeResidueIndicatorB_eq_projected_product]
    apply Finset.prod_congr rfl
    intro r _
    simp only [actualMixedSquareIndicator,mixedPairEquiv,representativeSquareProjectionB]
    erw [DiagonalSmallResidueNorm.crtPairEquiv_fst,DiagonalSmallResidueNorm.crtPairEquiv_snd_coe]
    rfl
  rw [he]
  erw [mixed_product_average]
  simp only [actualMixedSquareIndicator_average]

theorem unit_B_average_eq_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    [NeZero (representativeModulus h k)] :
    average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      ((∏r : Representative h k,actualUnitSquareProbability h k hs ks r):ℂ) :=
  unit_B_average_eq_product_of_coprime h k hs ks had.2.1

theorem mixed_B_average_eq_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    [NeZero (representativeModulus h k)] :
    average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2))=
      ((∏r : Representative h k,actualMixedSquareProbability h k hs ks r):ℂ) :=
  mixed_B_average_eq_product_of_coprime h k hs ks had.2.1

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
