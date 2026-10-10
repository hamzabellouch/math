import Mathlib
import OAI.Computability.QuantumFactoring.TableOrderCircuit

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

/-- The extra n bits make zero-extension unconditional, including empty
malformed tables. On verified input this holds the entire repeated product. -/
def tableOrderWidth (n f : ℕ) : ℕ := n*(n*f)+n+1

def tableOrderPrimes {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k (tableOrderWidth n (tableNets rows).length)) :=
  List.flatten (List.replicate n ((tableNets rows).map (fun p=>
    p.comp (resizeWord n (tableOrderWidth n (tableNets rows).length)))))

lemma tableOrderPrimes_values {k n : ℕ} (hn : 2 ≤ n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      List.flatten (List.replicate n (PhysicalTree.tableFactors (tableValues rows x))) := by
  have hw : n ≤ tableOrderWidth n (tableNets rows).length := by
    dsimp only [tableOrderWidth]
    omega
  simp only [tableOrderPrimes,List.map_flatten,List.map_replicate,List.map_map,
    Function.comp_def,eval_comp,resizeWord_toNat hw]
  rw [tableNets_values hn]

lemma tableOrderPrimes_length {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    (tableOrderPrimes rows).length=n*(tableNets rows).length := by
  simp only [tableOrderPrimes,List.length_flatten,List.map_replicate,List.length_map,
    List.sum_replicate,smul_eq_mul]

lemma tableOrderPrimes_product_bound {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    ((tableOrderPrimes rows).map (fun p=>(bitsValue (p.eval x)).toNat)).prod < 2^(tableOrderWidth n (tableNets rows).length) := by
  have h : ∀ p∈tableOrderPrimes rows,(bitsValue (p.eval x)).toNat ≤ 2^n := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,_hr,rfl⟩:=List.mem_map.mp hp
    rw [eval_comp,resizeWord_toNat (by dsimp [tableOrderWidth];omega)]
    exact (bitsValue (r.eval x)).isLt.le
  have hb:=word_list_product_bound (tableOrderPrimes rows) x h
  rw [tableOrderPrimes_length] at hb
  exact hb.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [tableOrderWidth];omega))

/-- A literal order circuit using only retained verified table entries and
modular powering. No mathematical factorization/support enumeration appears in
its definition, even on malformed inputs. -/
def tableOrder {k n : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  let w:=tableOrderWidth n (tableNets rows).length
  (orderFromList (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows)).comp (resizeWord w n)

theorem tableOrder_exact {k n N M m : ℕ} (hn : 2 ≤ n)
    (aN mN : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k)
    (h : PhysicalTree.CompleteLog n N (tableValues rows x))
    (hM : M∈(tableValues rows x).map Prod.fst) (hM0 : M≠0)
    (hm : 2 ≤ m) (hd : m∣M) (u : (ZMod m)ˣ)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    (bitsValue ((tableOrder aN mN rows).eval x)).toNat=orderOf u := by
  let w:=tableOrderWidth n (tableNets rows).length
  have hwide : n ≤ w := by dsimp [w,tableOrderWidth];omega
  have hv:=orderFromList_unit hm (aN.comp (resizeWord n w)) (mN.comp (resizeWord n w))
    u (tableOrderPrimes rows) x
    (by simpa only [eval_comp,resizeWord_toNat hwide] using ha)
    (by simpa only [eval_comp,resizeWord_toNat hwide] using hmN)
    (tableOrderPrimes_product_bound rows x)
  rw [tableOrderPrimes_values hn] at hv
  have hb : m < 2^n := by rw [←hmN];exact (bitsValue (mN.eval x)).isLt
  have hs:=PhysicalTree.table_strip_order h hM hM0 hm hb hd u
  rw [List.prod_flatten,List.map_replicate,List.prod_replicate,hs] at hv
  have hord : orderOf u < 2^n := by
    let : NeZero m:=⟨by omega⟩
    have hh : orderOf u ≤ m.totient := by
      simpa only [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] using (orderOf_le_card (x := u))
    exact (hh.trans (Nat.totient_le m)).trans_lt hb
  rw [tableOrder,eval_comp,resizeWord_value,BitVec.toNat_setWidth,hv,Nat.mod_eq_of_lt hord]

/-- This bound is polynomial in n, table length and the individual stored-word
circuit cost. Resizing is itself a bounded circuit, not a word-RAM primitive. -/
def tableOrderBound (n f c : ℕ) : ℕ :=
  let w:=tableOrderWidth n f
  let C:=3*c+220*n+50+w
  (n*f)*(C+90*w*w+14*w+6+stripStepBound w C)+w+n

lemma tableOrder_count {k n c : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c)
    (hr : ∀ r∈rows,r.1.net.count ≤ c ∧ ∀ p∈r.2,p.net.count ≤ c) :
    (tableOrder a m rows).net.count ≤ tableOrderBound n (tableNets rows).length c := by
  let w:=tableOrderWidth n (tableNets rows).length
  let C:=3*c+220*n+50+w
  have hres:=resizeWord_count n w
  have hp : ∀ p∈tableOrderPrimes rows,p.net.count ≤ C := by
    intro p hp
    obtain ⟨ps,hps,hp⟩:=List.mem_flatten.mp hp
    have he:=(List.mem_replicate.mp hps).2
    subst ps
    obtain ⟨r,hr',rfl⟩:=List.mem_map.mp hp
    have H:=tableNets_counts rows hr r hr'
    rw [count_comp]
    exact Nat.add_le_add H hres
  have hs:=orderFromList_count (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows) (c:=C)
    (by rw [count_comp];dsimp [C];omega)
    (by rw [count_comp];dsimp [C];omega) hp
  rw [tableOrderPrimes_length] at hs
  have hsmall:=resizeWord_count w n
  change _ ≤ _+n
  simp only [tableOrder,count_comp]
  exact Nat.add_le_add hs hsmall

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
