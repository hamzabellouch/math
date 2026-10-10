import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegration

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open Construction ResidueHaar HistoryPairRepresentatives HistoryPairRows
open HistoryRepresentativeSourceSeparation
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem average_mul_left {α : Type*} [Fintype α] (c : ℂ) (f : α → ℂ) :
    average (fun x => c*f x)=c*average f := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem occurrence_product_eq_multiplicity (h g : History l) :
    (∏ i : Occurrences h g,((slot h g i).value:ℂ)) =
      ∏ r : Representative h g,(prime h g r:ℂ)^
        RepeatedLabels.multiplicity Finset.univ (label h g) r := by
  classical
  exact RepeatedLabels.product_by_multiplicity Finset.univ (label h g)
    (fun r => (prime h g r:ℂ))

theorem representative_unit_joint_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside)
    (F : (∀ r : Representative h g,UnitPair ((prime h g r)^2)) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : UnitPair (∏ r : Representative h g,(prime h g r)^2) =>
      F (unitPairEquiv _ hp.2.1 z))=average F := by
  let := representativeSquaresNeZero h g hs gs
  exact unit_joint_average _ hp.2.1 F

theorem representative_mixed_joint_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside)
    (F : (∀ r : Representative h g,MixedPair ((prime h g r)^2)) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : MixedPair (∏ r : Representative h g,(prime h g r)^2) =>
      F (mixedPairEquiv _ hp.2.1 z))=average F := by
  let := representativeSquaresNeZero h g hs gs
  exact mixed_joint_average _ hp.2.1 F

theorem representative_unit_weighted_product_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside)
    (f : ∀ r : Representative h g,UnitPair ((prime h g r)^2) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : UnitPair (∏ r : Representative h g,(prime h g r)^2) =>
      (∏ i : Occurrences h g,((slot h g i).value:ℂ)) *
        ∏ r,f r (unitPairEquiv _ hp.2.1 z r)) =
      (∏ r : Representative h g,(prime h g r:ℂ)^
        RepeatedLabels.multiplicity Finset.univ (label h g) r) * ∏ r,average (f r) := by
  let := representativeSquaresNeZero h g hs gs
  rw [average_mul_left,unit_product_average,occurrence_product_eq_multiplicity]

theorem representative_mixed_weighted_product_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside)
    (f : ∀ r : Representative h g,MixedPair ((prime h g r)^2) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : MixedPair (∏ r : Representative h g,(prime h g r)^2) =>
      (∏ i : Occurrences h g,((slot h g i).value:ℂ)) *
        ∏ r,f r (mixedPairEquiv _ hp.2.1 z r)) =
      (∏ r : Representative h g,(prime h g r:ℂ)^
        RepeatedLabels.multiplicity Finset.univ (label h g) r) * ∏ r,average (f r) := by
  let := representativeSquaresNeZero h g hs gs
  rw [average_mul_left,mixed_product_average,occurrence_product_eq_multiplicity]

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
