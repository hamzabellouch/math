import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageFactor

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCRTIntegration HistorySignedResidueFactorization ResidueHaar
open HistoryPairSquareProbability HistoryBulkReferenceTests
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem unit_B_averageAt_eq_product_of_coprime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (hc : Pairwise (fun r t : Representative h k => ((prime h k r)^2).Coprime ((prime h k t)^2)))
    [NeZero (representativeModulus h k)] :
    average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      ((∏r : Representative h k,actualUnitSquareProbabilityAt h k hs ks v r):ℂ) := by
  let := representativeSquaresNeZero h k hs ks
  have he : (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      (fun z => ∏r : Representative h k,actualUnitSquareIndicatorAt h k hs ks v r
        (unitPairEquiv (fun r : Representative h k => (prime h k r)^2) hc z r)) := by
    funext z
    rw [primeResidueIndicatorAt_eq_projected_product]
    apply Finset.prod_congr rfl
    intro r _
    simp only [actualUnitSquareIndicatorAt,representativeSquareProjectionB]
    erw [unitPairEquiv_fst_coe,unitPairEquiv_snd_coe]
    rfl
  rw [he]
  erw [unit_product_average]
  simp only [actualUnitSquareIndicatorAt_average]

theorem mixed_B_averageAt_eq_product_of_coprime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (hc : Pairwise (fun r t : Representative h k => ((prime h k r)^2).Coprime ((prime h k t)^2)))
    [NeZero (representativeModulus h k)] :
    average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      ((∏r : Representative h k,actualMixedSquareProbabilityAt h k hs ks v r):ℂ) := by
  let := representativeSquaresNeZero h k hs ks
  have he : (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      (fun z => ∏r : Representative h k,actualMixedSquareIndicatorAt h k hs ks v r
        (mixedPairEquiv (fun r : Representative h k => (prime h k r)^2) hc z r)) := by
    funext z
    rw [primeResidueIndicatorAt_eq_projected_product]
    apply Finset.prod_congr rfl
    intro r _
    simp only [actualMixedSquareIndicatorAt,mixedPairEquiv,representativeSquareProjectionB]
    erw [DiagonalSmallResidueNorm.crtPairEquiv_fst,DiagonalSmallResidueNorm.crtPairEquiv_snd_coe]
    rfl
  rw [he]
  erw [mixed_product_average]
  simp only [actualMixedSquareIndicatorAt_average]

theorem unit_B_averageAt_eq_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    [NeZero (representativeModulus h k)] :
    average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      ((∏r : Representative h k,actualUnitSquareProbabilityAt h k hs ks v r):ℂ) :=
  unit_B_averageAt_eq_product_of_coprime h k hs ks v had.2.1

theorem mixed_B_averageAt_eq_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    [NeZero (representativeModulus h k)] :
    average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))=
      ((∏r : Representative h k,actualMixedSquareProbabilityAt h k hs ks v r):ℂ) :=
  mixed_B_averageAt_eq_product_of_coprime h k hs ks v had.2.1

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
