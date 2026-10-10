import Mathlib
import OAI.Computability.QuantumFactoring.TableOrderCircuit
import OAI.Computability.QuantumFactoring.TotientCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- Run the polynomial accumulator scan from the queried word and one. -/
def totientFromList {k w : ℕ} (v : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (v.pair (wordConstant (BitVec.ofNat w 1)))).comp
    (totientScanNet qs)).comp (select (fun i=>Fin.natAdd k (Fin.natAdd w i)))

lemma totientFromList_value {k w : ℕ} (hw : 0 < w) (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((totientFromList v qs).eval x)).toNat=
      totientScan (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (v.eval x)).toNat % 2^w := by
  let one : Basis w:=(wordConstant (n:=k) (BitVec.ofNat w 1)).eval x
  let s:=Fin.append (v.eval x) one
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  have hs : ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat)=
      ((bitsValue (v.eval x)).toNat,1) := by
    have hl : s ∘ Fin.castAdd w=v.eval x := by funext i; exact Fin.append_left _ _ i
    have hr : s ∘ Fin.natAdd w=one := by funext i; exact Fin.append_right _ _ i
    rw [hl,hr]
    simp only [one,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  obtain ⟨s',he,hv⟩:=totientScanNet_value hw qs x s
  rw [hs] at hv
  have hv':=congrArg Prod.snd hv
  rw [totientFoldNat_score _ _ (_,1) h1,one_mul] at hv'
  have houtput : Fin.append x s' ∘ (fun i=>Fin.natAdd k (Fin.natAdd w i))=s' ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  rw [totientFromList,eval_comp,eval_comp,eval_pair,eval_pair,eval_select]
  change (bitsValue ((select (fun i=>Fin.natAdd k (Fin.natAdd w i))).eval
    ((totientScanNet qs).eval (Fin.append x s)))).toNat=_
  rw [he,eval_select,houtput]
  exact hv'

lemma totientFromList_count {k w c : ℕ} (v : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientFromList v qs).net.count ≤ v.net.count+w+qs.length*totientStepBound w c := by
  have hh:=totientScanNet_count qs hq
  simp only [totientFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero,
    wordConstant_count]
  omega

/-- At most n repetitions of each rectangular prime entry suffice. Unlike
order stripping, the totient accumulator does not need a wide product. -/
def tableTotient {k n : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  totientFromList v (List.flatten (List.replicate n (tableNets rows)))

theorem tableTotient_exact {k n N M m d : ℕ} (hn : 2 ≤ n) (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (hc : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hd : m∣M) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval x)).toNat=d) :
    (bitsValue ((tableTotient v rows).eval x)).toNat=d.totient := by
  rw [tableTotient,totientFromList_value (by omega),List.map_flatten,List.map_replicate,
    tableNets_values hn,hv,PhysicalTree.table_totient_exact hc hM hM0 hm hb hd hd0 hdt]
  have hdB : d < 2^n := by rw [←hv]; exact (bitsValue (v.eval x)).isLt
  exact Nat.mod_eq_of_lt ((Nat.totient_le d).trans_lt hdB)

def tableTotientBound (n f c : ℕ) : ℕ := c+n+(n*f)*totientStepBound n (3*c+220*n+50)

lemma tableTotient_count {k n c : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hv : v.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableTotient v rows).net.count ≤ tableTotientBound n (tableNets rows).length c := by
  have hp : ∀ p∈List.flatten (List.replicate n (tableNets rows)),p.net.count ≤ 3*c+220*n+50 := by
    intro p hp
    obtain ⟨qs,hqs,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact tableNets_counts rows hr p hp
  have hh:=totientFromList_count v _ hp
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by dsimp only [tableTotientBound];omega)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
