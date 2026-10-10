import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveSlots
import OAI.Computability.QuantumFactoring.FlatDataView

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial
namespace DataView
variable {d : FactorData} {M : ℕ} (h : DataView d M)
include h

lemma residueGood {m : ℕ} (hM : 0 < M) (hd : m ∣ M) (a : ℕ) :
    dataResidueGood d a m ↔ dataResidueGood (trueData M) a m := by
  have ho (p : ℕ) : dataOrder d a (p^m.factorization p)=
      dataOrder (trueData M) a (p^m.factorization p) :=
    h.order _ _ hM ((Nat.ordProj_dvd m p).trans hd)
  simp only [dataResidueGood,h.record,dataRecord_correct hM hd,ho]

lemma canonicalResidue (a m : ℕ) :
    dataCanonicalResidue d a m ↔ dataCanonicalResidue (trueData M) a m := by
  simp only [dataCanonicalResidue,h.record]

lemma goodList {m : ℕ} (hM : 0 < M) (hd : m ∣ M) (n : ℕ)
    (y : Basis (Completion.transitionWidth n)) :
    dataGoodList d m n y ↔ dataGoodList (trueData M) m n y := by
  simp only [dataGoodList,h.residueGood hM hd]

lemma canonicalList (m n : ℕ) (hn : 0 < n) (y : Basis (Completion.transitionWidth n)) :
    dataCanonicalList d m n hn y ↔ dataCanonicalList (trueData M) m n hn y := by
  simp only [dataCanonicalList,h.canonicalResidue]

lemma listPassed {n : ℕ} (hM : 0 < M) (m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : PhysicalListSlots.Result n) :
    dataListPassed d m hn r ↔ dataListPassed (trueData M) m hn r := by
  have hg : (fun x=>dataGoodList d (bitsValue m).toNat n (PhysicalListSlots.ordinary x))=
      (fun x=>dataGoodList (trueData M) (bitsValue m).toNat n (PhysicalListSlots.ordinary x)) := by
    funext x
    exact propext (h.goodList hM hd n _)
  have hc : dataCanonicalList d (bitsValue m).toNat n hn=
      dataCanonicalList (trueData M) (bitsValue m).toNat n hn := by
    funext y
    exact propext (h.canonicalList _ n hn y)
  rw [dataListPassed,dataListPassed,hg,hc,h.listSuccess]

lemma orderPassed {n : ℕ} (hM : 0 < M) (a m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (r : OrderSlots.Result n) : dataOrderPassed d a m r ↔ dataOrderPassed (trueData M) a m r := by
  classical
  simp only [dataOrderPassed,h.order _ _ hM hd,h.orderSuccess _ _ _ hM hd]

lemma splitPassed {n : ℕ} (hM : 0 < M) (m : Basis n) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : UniversalSplit.Raw n) :
    dataSplitPassed d m hn r ↔ dataSplitPassed (trueData M) m hn r := by
  classical
  simp only [dataSplitPassed,h.listPassed hM m hd hn,h.orderPassed hM _ m hd]

/-- Actual verified data give the ideal local event on exactly the same retained
outcome. The statement covers all nonzero divisors of a verified node. -/
theorem splitPassed_correct {n : ℕ} (hM : 0 < M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat ∣ M)
    (hn : 0 < n) (r : UniversalSplit.Raw n) :
    dataSplitPassed d m hn r ↔ UniversalSplit.passed m r := by
  rw [h.splitPassed hM m hd hn]
  exact dataSplitPassed_correct hM m hm hd hn r
end DataView
end ExactQuantumFactoring


end

end OAI
