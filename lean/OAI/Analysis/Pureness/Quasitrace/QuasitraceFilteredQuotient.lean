import OAI.Analysis.Pureness.Quasitrace.QuasitraceFilteredNull
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal

variable {ι : Type*} {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)]

instance boundedProductCStarAlgebra : CStarAlgebra (lp D ∞) where

instance boundedProductPartialOrder : PartialOrder (lp D ∞) :=
  CStarAlgebra.spectralOrder _
instance boundedProductStarOrderedRing : StarOrderedRing (lp D ∞) :=
  CStarAlgebra.spectralOrderedRing _

variable (T : ∀ i, PositiveQuasitrace (D i)) (F : Filter ι)
variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x + (T i).metricSize y)
variable (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)

def filteredQuasitraceClosedIdeal : ClosedStarIdeal (lp D ∞) where
  ideal := filteredQuasitraceNullIdeal T F hadd
  star_mem := filteredQuasitraceNullIdeal_star T F hadd
  isClosed := filteredQuasitraceNullIdeal_isClosed T F hadd hunit

abbrev FilteredQuasitraceQuotient := (filteredQuasitraceClosedIdeal T F hadd hunit).Quotient

def filteredQuasitraceQuotientMap : lp D ∞ →⋆ₐ[ℂ] FilteredQuasitraceQuotient T F hadd hunit :=
  (filteredQuasitraceClosedIdeal T F hadd hunit).quotientStarHom

lemma filteredQuasitraceQuotientMap_eq_zero (u : lp D ∞) :
    filteredQuasitraceQuotientMap T F hadd hunit u = 0 ↔
      Tendsto (fun i => T i (Positive.starMul (u i))) F (nhds 0) := by
  change (filteredQuasitraceNullIdeal T F hadd).ringCon.mk' u =
    (filteredQuasitraceNullIdeal T F hadd).ringCon.mk' 0 ↔ _
  exact (show (filteredQuasitraceNullIdeal T F hadd).ringCon.mk' u =
    (filteredQuasitraceNullIdeal T F hadd).ringCon.mk' 0 ↔
      u ∈ filteredQuasitraceNullIdeal T F hadd from Quotient.eq).trans
        (filteredQuasitraceNullIdeal_mem T F hadd u)

lemma filteredQuasitraceQuotientMap_eq (u v : lp D ∞) :
    filteredQuasitraceQuotientMap T F hadd hunit u =
      filteredQuasitraceQuotientMap T F hadd hunit v ↔
        Tendsto (fun i => T i (Positive.starMul (u i-v i))) F (nhds 0) := by
  simpa only [map_sub, sub_eq_zero, lp.coeFn_sub, Pi.sub_apply] using
    filteredQuasitraceQuotientMap_eq_zero T F hadd hunit (u - v)

instance filteredQuasitraceQuotientNontrivial [F.NeBot] :
    Nontrivial (FilteredQuasitraceQuotient T F hadd hunit) := by
  apply nontrivial_of_ne (1 : FilteredQuasitraceQuotient T F hadd hunit) 0
  intro h
  have hm : (filteredQuasitraceNullIdeal T F hadd).ringCon (1 : lp D ∞) 0 := by
    apply Quotient.exact
    exact h
  exact filteredQuasitraceNullIdeal_one_not_mem T F hadd hunit hm

lemma filteredQuasitraceQuotient_norm_square
    (x : FilteredQuasitraceQuotient T F hadd hunit) :
    ‖star x*x‖ = ‖x‖*‖x‖ := CStarRing.norm_star_mul_self
end CuntzPureness

end

end OAI
