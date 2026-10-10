import Mathlib
import OAI.Computability.QuantumFactoring.FlatVerifiedData
import OAI.Computability.QuantumFactoring.RetrospectiveStatistics

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- Precisely the supplied local record and p−1 lookup facts consumed by the
retrospective arithmetic. This is established below from actual verified rows. -/
def DataView (d : FactorData) (M : ℕ) : Prop :=
  d.factors=M.factorization ∧
    ∀ l∈children M,dataChildPrimes d l=recordPrimes l.factorization

lemma trueData_view (M : ℕ) : DataView (trueData M) M := by
  refine ⟨trueData_factors M,?_⟩
  intro l hl
  cases hf : ((children M).map trueData).find? (fun d=>decide (d.label=l)) with
  | none=>
    have hh:=List.find?_eq_none.mp hf (trueData l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    simp only [trueData_label,decide_true] at hh
    contradiction
  | some d=>
    obtain ⟨a,_ha,he⟩:=List.mem_map.mp (List.mem_of_find?_eq_some hf)
    subst d
    have he : a=l := by simpa only [trueData_label,decide_eq_true_eq] using List.find?_some hf
    subst a
    simp only [dataChildPrimes,trueData_descendants,hf,trueData_factors]

namespace PhysicalTree
noncomputable def rowData (r : ℕ×List ℕ) : FactorData :=
  .node r.1 (primeRecord (r.2.filter (fun p=>decide (p≠0)))) []
noncomputable def flatData (rows : List (ℕ×List ℕ)) (M : ℕ) : FactorData :=
  .node M (primeRecord (lookupPrimes rows M)) (rows.map rowData)
@[simp] lemma rowData_label (r : ℕ×List ℕ) : (rowData r).label=r.1 := rfl
lemma rowData_factors {r : ℕ×List ℕ} {n : ℕ} (h : CorrectEncoding r.1 n r.2) :
    (rowData r).factors=r.1.factorization := by
  have hh:=encoding_filter h
  change primeRecord _=_
  rw [primeRecord_eq_factorization _ hh.1,hh.2]

/-- The read-only view is constructed solely by projection of retained fields.
No trueData or factorization operation occurs in its definition. -/
theorem completeLog_view {n N M : ℕ} {rows : List (ℕ×List ℕ)}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0) :
    DataView (flatData rows M) M := by
  refine ⟨?_,?_⟩
  · have hh:=lookupPrimes_correct h hM hpos
    change primeRecord _=_
    rw [primeRecord_eq_factorization _ hh.1,hh.2]
  · intro l hl
    have hlpos : l≠0 := by have hh:=(child_bounds hl).1;omega
    have hlmem:=log_child_present h hM hl
    cases hf : (rows.map rowData).find? (fun d=>decide (d.label=l)) with
    | none=>
      obtain ⟨r,hr,he⟩:=List.mem_map.mp hlmem
      have hh:=List.find?_eq_none.mp hf (rowData r) (List.mem_map.mpr ⟨r,hr,rfl⟩)
      simp only [rowData_label,he,decide_true] at hh
      contradiction
    | some d=>
      obtain ⟨r,hr,he⟩:=List.mem_map.mp (List.mem_of_find?_eq_some hf)
      subst d
      have hh : decide ((rowData r).label=l)=true := List.find?_some (p := fun d : FactorData => decide (d.label=l)) (a := rowData r) hf
      have he : r.1=l := (decide_eq_true_eq).mp hh
      have hv : CorrectEncoding r.1 n r.2 := (h.2.1 r hr).resolve_left (by rwa [he])
      change (match (rows.map rowData).find? (fun d=>decide (d.label=l)) with
        | none=>[] | some d=>recordPrimes d.factors)=_
      simp only [hf,rowData_factors hv,he]
end PhysicalTree

namespace DataView
variable {d : FactorData} {M : ℕ} (h : DataView d M)
include h

lemma divisorPrimes (m : ℕ) : dataDivisorPrimes d m=dataDivisorPrimes (trueData M) m := by
  simp only [dataDivisorPrimes,h.1,trueData_factors]
lemma record (m : ℕ) : dataRecord d m=dataRecord (trueData M) m := by
  rw [dataRecord,dataRecord,h.divisorPrimes]
lemma phi (m : ℕ) : dataPhi d m=dataPhi (trueData M) m := by
  rw [dataPhi,dataPhi,h.record]
lemma favorable (m n : ℕ) : dataFavorable d m n=dataFavorable (trueData M) m n := by
  rw [dataFavorable,dataFavorable,h.record]
lemma childPrimes {l : ℕ} (hl : l∈children M) :
    dataChildPrimes d l=dataChildPrimes (trueData M) l := by
  rw [h.2 l hl,(trueData_view M).2 l hl]
lemma totientPrimes {m : ℕ} (hM : 0 < M) (hd : m ∣ M) :
    dataTotientPrimes d m=dataTotientPrimes (trueData M) m := by
  have hf : primeRecord (dataDivisorPrimes (trueData M) m)=m.factorization := dataRecord_correct hM hd
  simp only [dataTotientPrimes,h.divisorPrimes,hf]
  apply List.flatMap_congr
  intro p hp
  by_cases h2 : p=2
  · simp only [ite_eq_left h2]
  · have hpm:=Nat.mem_primeFactors.mp ((Finset.mem_sort (· ≤ ·)).mp hp)
    have hc : p-1∈children M := mem_children.mpr
      ⟨p,hpm.1,hpm.2.1.trans hd,hM.ne',by have hh:=hpm.1.two_le;omega,rfl⟩
    rw [ite_eq_right h2,ite_eq_right h2,h.childPrimes hc]
lemma order (a m : ℕ) (hM : 0 < M) (hd : m ∣ M) : dataOrder d a m=dataOrder (trueData M) a m := by
  rw [dataOrder,dataOrder,h.totientPrimes hM hd,h.phi]
lemma listSuccess (m n K : ℕ) : dataListSuccess d m n K=dataListSuccess (trueData M) m n K := by
  rw [dataListSuccess,dataListSuccess,h.favorable]
lemma orderSuccess (a m K : ℕ) (hM : 0 < M) (hd : m ∣ M) :
    dataOrderSuccess d a m K=dataOrderSuccess (trueData M) a m K := by
  rw [dataOrderSuccess,dataOrderSuccess,h.order a m hM hd]
end DataView
end ExactQuantumFactoring


end

end OAI
