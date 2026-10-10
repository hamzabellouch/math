import Mathlib
import OAI.Computability.QuantumFactoring.AuxiliaryTree

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- The source's distinct positive-exponent factor records. Finsupp stores each
prime once; its canonical serialization sorts its support in increasing order. -/
abbrev FactorRecord := ℕ→₀ℕ

def factorRecordList (f : FactorRecord) : List (ℕ×ℕ) :=
  (f.support.sort (· ≤ ·)).map (fun p => (p,f p))

def recordChildren (f : FactorRecord) : List ℕ :=
  ((f.support.filter (fun p => 2 < p)).sort (· ≤ ·)).map (·-1)

inductive FactorData where
  | node (label : ℕ) (factors : FactorRecord) (descendants : List FactorData) : FactorData

def FactorData.label : FactorData→ℕ
  | .node m _ _ => m

def trueData (m : ℕ) : FactorData :=
  .node m m.factorization ((children m).attach.map (fun d => trueData d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

lemma trueData_eq (m : ℕ) : trueData m =
    .node m m.factorization ((children m).map trueData) := by
  rw [trueData]
  congr 1
  simp only [List.attach_map_val]

@[simp] lemma trueData_label (m : ℕ) : (trueData m).label=m := by
  rw [trueData_eq]; rfl

lemma recordChildren_factorization (m : ℕ) : recordChildren m.factorization=children m := rfl

/-- Complete-data acceptance. The local tests are finite prime checks and a
product check, followed by EXACT ordered children; no witness fields or advice. -/
inductive FactorData.Valid : FactorData→Prop where
  | node (m : ℕ) (f : FactorRecord) (ds : List FactorData)
      (hm : 2 ≤ m) (hp : ∀ p∈f.support,p.Prime) (hprod : f.prod (·^·)=m)
      (hlabels : ds.map FactorData.label=recordChildren f)
      (hchildren : ∀ d∈ds, FactorData.Valid d) : FactorData.Valid (.node m f ds)

lemma valid_factorRecord {m : ℕ} {f : FactorRecord}
    (hp : ∀ p∈f.support,p.Prime) (hprod : f.prod (·^·)=m) : f=m.factorization := by
  rw [← hprod,Nat.prod_pow_factorization_eq_self hp]

/-- Unique prime factorization makes the entire ordered occurrence tree unique;
equal child labels under different parents remain separate list occurrences. -/
theorem valid_eq_trueData {d : FactorData} (hd : d.Valid) : d=trueData d.label := by
  induction hd with
  | node m f ds hm hp hprod hlabels _ ih =>
    have hf := valid_factorRecord hp hprod
    have hds : ds=(children m).map trueData := by
      have hh : ds.map (fun d => trueData d.label)=ds := by
        calc
          _ = ds.map id := List.map_congr_left (fun d hd => (ih d hd).symm)
          _ = ds := List.map_id ds
      calc
        ds = ds.map (fun d => trueData d.label) := hh.symm
        _ = (ds.map FactorData.label).map trueData := List.map_map.symm
        _ = (children m).map trueData := by rw [hlabels,hf,recordChildren_factorization]
    rw [hf,hds]
    exact (trueData_eq m).symm

/-- The canonical data are always complete; recursion is justified by the
literal source decrease p−1<m, not a guessed tree. -/
theorem trueData_valid {m : ℕ} (hm : 2 ≤ m) : (trueData m).Valid := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [trueData_eq]
    apply FactorData.Valid.node m m.factorization ((children m).map trueData) hm
    · intro p hp
      exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prod_factorization_pow_eq_self (by omega)
    · simp only [List.map_map,Function.comp_def,trueData_label,recordChildren_factorization]
      exact List.map_id (children m)
    · intro d hd
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
      exact ih a (child_bounds ha).2 (child_bounds ha).1

theorem valid_iff_trueData {m : ℕ} (hm : 2 ≤ m) (d : FactorData) (hl : d.label=m) :
    d.Valid ↔ d=trueData m := by
  constructor
  · intro hd
    simpa only [hl] using valid_eq_trueData hd
  · rintro rfl
    exact trueData_valid hm

end ExactQuantumFactoring


end

end OAI
