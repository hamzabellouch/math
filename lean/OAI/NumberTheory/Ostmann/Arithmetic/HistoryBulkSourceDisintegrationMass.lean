import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSourceDisintegration
open Construction Conclusion
variable (sources : SourceFamily) (T : List SourceSlot) (bulk : PrimeSource)
variable (hbulk : ∀i : BulkPosition T, sources (T.get i.val).origin = bulk)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : BulkPosition T ≃ ι)

theorem coordinateEquiv_mass (x : SourceAssignment sources T) :
    (assignmentPrior sources T).mass x =
      (nonbulkPrior sources T).mass (coordinateEquiv sources T bulk hbulk e x).1 *
      (bulkPrior bulk ι).mass (coordinateEquiv sources T bulk hbulk e x).2 := by
  have hb : (bulkPrior bulk ι).mass (coordinateEquiv sources T bulk hbulk e x).2 =
      ∏ i : BulkPosition T, (sources (T.get i.val).origin).law.mass (x i.val) := by
    change (∏u : ι, bulk.law.mass ((coordinateEquiv sources T bulk hbulk e x).2 u)) = _
    rw [←e.prod_comp (fun u => bulk.law.mass ((coordinateEquiv sources T bulk hbulk e x).2 u))]
    simp only [coordinateEquiv_bulk_mass]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun j : BulkPosition T =>
      (sources (T.get j.val).origin).law.mass (x j.val)) (e.symm_apply_apply i)
  rw [hb]
  change (∏i : Fin T.length, (sources (T.get i).origin).law.mass (x i)) =
    (∏i : NonbulkPosition T, (sources (T.get i.val).origin).law.mass (x i.val)) *
    ∏i : BulkPosition T, (sources (T.get i.val).origin).law.mass (x i.val)
  rw [mul_comm]
  exact (Fintype.prod_subtype_mul_prod_subtype
    (fun i : Fin T.length => (T.get i).role = .bulk)
    (fun i => (sources (T.get i).origin).law.mass (x i))).symm

def coordinateWeightEquiv : WeightEquiv (assignmentPrior sources T).mass
    (fun y : NonbulkSample sources T × (ι → bulk.Sample) =>
      (nonbulkPrior sources T).mass y.1 * (bulkPrior bulk ι).mass y.2) :=
  ⟨coordinateEquiv sources T bulk hbulk e,coordinateEquiv_mass sources T bulk hbulk e⟩

theorem coordinateEquiv_cmean
    (F : NonbulkSample sources T × (ι → bulk.Sample) → ℂ) :
    (assignmentPrior sources T).cmean (fun x => F (coordinateEquiv sources T bulk hbulk e x)) =
      (nonbulkPrior sources T).cmean (fun a => (bulkPrior bulk ι).cmean (fun y => F (a,y))) := by
  have h := (coordinateWeightEquiv sources T bulk hbulk e).csum_comp F
  simpa only [FinitePrior.cmean,Fintype.sum_prod_type,Complex.ofReal_mul,
    Finset.mul_sum,mul_assoc,coordinateWeightEquiv] using h

theorem source_cmean_disintegration (F : SourceAssignment sources T → ℂ) :
    (assignmentPrior sources T).cmean F =
      (nonbulkPrior sources T).cmean (fun a => (bulkPrior bulk ι).cmean (fun y =>
        F ((coordinateEquiv sources T bulk hbulk e).symm (a,y)))) := by
  simpa only [Equiv.symm_apply_apply] using coordinateEquiv_cmean sources T bulk hbulk e
    (fun y => F ((coordinateEquiv sources T bulk hbulk e).symm y))

end Ostmann.Arithmetic.HistoryBulkSourceDisintegration

end

end OAI
