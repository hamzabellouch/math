import Mathlib
import OAI.Computability.QuantumFactoring.TableOrder

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

/-- A zero/unused-row word is replaced by the harmless prime 2. -/
def tableFactor {k n : ℕ} (label p : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux ((zeroWord label).bor (zeroWord p)) (wordConstant 2) p

lemma tableFactor_value {k n : ℕ} (hn : 2≤n) (label p : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((tableFactor label p).eval x)).toNat=
      if (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 then 2
      else (bitsValue (p.eval x)).toNat := by
  have hb : 2<2^n := lt_of_lt_of_le (by norm_num : 2<2^2) (Nat.pow_le_pow_right (by norm_num) hn)
  have hh : ((zeroWord label).bor (zeroWord p)).eval x 0=true ↔
      (bitsValue (label.eval x)).toNat=0 ∨ (bitsValue (p.eval x)).toNat=0 := by
    rw [eval_bor,Bool.or_eq_true,zeroWord_value,zeroWord_value]
  rw [tableFactor,wordMux_eval]
  by_cases h : ((zeroWord label).bor (zeroWord p)).eval x 0=true
  · rw [ite_eq_left h,ite_eq_left (hh.mp h),wordConstant_eval]
    exact Nat.mod_eq_of_lt hb
  · rw [ite_eq_right h,ite_eq_right (fun h' => h (hh.mpr h'))]

lemma tableFactor_count {k n : ℕ} (label p : BooleanNetwork k n) :
    (tableFactor label p).net.count≤label.net.count+2*p.net.count+220*n+50 := by
  have hl:=zeroWord_count label
  have hp:=zeroWord_count p
  simp only [tableFactor,wordMux_count,count_bor,wordConstant_count]
  omega

def tableNets {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k n) := rows.flatMap (fun r=>r.2.map (tableFactor r.1))

def tableValues {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    List (ℕ×List ℕ) := rows.map (fun r=>((bitsValue (r.1.eval x)).toNat,
      r.2.map (fun p=>(bitsValue (p.eval x)).toNat)))

lemma tableNets_values {k n : ℕ} (hn : 2≤n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    (tableNets rows).map (fun p=>(bitsValue (p.eval x)).toNat)=
      PhysicalTree.tableFactors (tableValues rows x) := by
  simp only [tableNets,tableValues,PhysicalTree.tableFactors,List.map_flatMap,List.flatMap_map,
    List.map_map,Function.comp_def,tableFactor_value hn]

lemma tableNets_counts {k n c : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n)))
    (hc : ∀ r∈rows,r.1.net.count≤c ∧ ∀ p∈r.2,p.net.count≤c) :
    ∀ p∈tableNets rows,p.net.count≤3*c+220*n+50 := by
  intro p hp
  obtain ⟨r,hr,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  have H:=hc r hr
  have Hq:=H.2 q hq
  exact (tableFactor_count r.1 q).trans (by omega)

/-- Start at the complete product of a known prime list and scan it once.
This is sufficient whenever the group order divides that product. -/
def orderFromList {k w : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (productNet qs)).comp (stripScan a m qs)).comp (select (Fin.natAdd k))

lemma orderFromList_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m)
    (hb : (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^w) :
    (bitsValue ((orderFromList aN mN qs).eval x)).toNat=
      stripOrderFactors u (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
        ((qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod) := by
  obtain ⟨z,he,hv⟩:=stripScan_unit hm aN mN u qs x ((productNet qs).eval x) ha hmN
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i;exact Fin.append_right _ _ i
  rw [orderFromList,eval_comp,eval_comp,eval_pair,eval_select]
  change (bitsValue ((select (Fin.natAdd k)).eval ((stripScan aN mN qs).eval
    (Fin.append x ((productNet qs).eval x))))).toNat=_
  rw [he,eval_select,hz,hv,productNet_nat,Nat.mod_eq_of_lt hb]

lemma orderFromList_count {k w c : ℕ} (a m : BooleanNetwork k w)
    (qs : List (BooleanNetwork k w)) (ha : a.net.count≤c) (hm : m.net.count≤c)
    (hq : ∀ q∈qs,q.net.count≤c) :
    (orderFromList a m qs).net.count≤
      qs.length*(c+90*w*w+14*w+6+stripStepBound w c)+w := by
  have hp:=productNet_count qs hq
  have hs:=stripScan_count a m qs ha hm hq
  simp only [orderFromList,count_comp,count_pair,count_select,zero_add,Nat.add_zero]
  nlinarith

/-- A uniform polynomial-width exact product bound. -/
lemma word_list_product_bound {k w n : ℕ} (qs : List (BooleanNetwork k w)) (x : Basis k)
    (h : ∀ q∈qs,(bitsValue (q.eval x)).toNat≤2^n) :
    (qs.map (fun q=>(bitsValue (q.eval x)).toNat)).prod<2^(n*qs.length+1) := by
  have hb:=List.prod_le_pow_length (qs.map (fun q=>(bitsValue (q.eval x)).toNat)) (2^n)
    (by intro p hp;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp;exact h q hq)
  rw [List.length_map,←pow_mul] at hb
  exact hb.trans_lt (Nat.pow_lt_pow_right (by omega : 1<2) (by omega))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
