import Mathlib
import OAI.Computability.DeterministicSum.CacheGather
import OAI.Computability.DeterministicSum.EvaluationTables
import OAI.Computability.DeterministicSum.SparsePolynomials

namespace OAI

/-! Source-identical evaluated coefficient rows and complete charged batch caching. -/

namespace DeterministicThreeSum.Structured.Indexed.Cache
open Axis SparseAxis DeterministicThreeSum.Rectangular Finset
open scoped BigOperators
noncomputable section

theorem Uvalue_source {T m b d D H : ℕ} (hm : 0 < m)
    (P : MvPolynomial (Fin d) (ZMod T)) (hP : P.totalDegree ≤ D) (a : ℕ → ℕ)
    (ha : ∀ (u : DigitBox m d) (v : DigitBox b d),
      (∑ k, (digitFunction m d u k).val)+(∑ k, (digitFunction b d v k).val) ≤ D →
      (a (lowCode (m*b) d (zipDigit m b d u v)):ZMod T)=
        Sparse.coefficient (ZMod T) m b P (digitFunction m d u) (digitFunction b d v))
    (j : DigitBox b d) (x : DigitBox m d) :
    (tensorValue T m m (powerTable T m) d
      (gathered false m b d D H (lowCode b d j) a) (lowCode m d x):ZMod T)=
        Weighted.U P (digitFunction b d j) (digitFunction m d x) := by
  rw [tensorValue_evaluation hm]
  unfold Weighted.U Weighted.monomial
  rw [← (digitFunctionEquiv m d).sum_comp]
  apply sum_congr rfl
  intro u _
  change _=Sparse.coefficient (ZMod T) m b P (digitFunction m d u) (digitFunction b d j)*_
  rw [gathered_U]
  split_ifs with h
  · rw [ha u j h]
    rfl
  · rw [Sparse.coefficient_support (ZMod T) P hP _ _ (by omega)]
    simp

theorem Wvalue_source {T m b d D : ℕ} (hb : 0 < b)
    (P : MvPolynomial (Fin d) (ZMod T)) (hP : P.totalDegree ≤ D) (a : ℕ → ℕ)
    (ha : ∀ (u : DigitBox m d) (v : DigitBox b d),
      (∑ k, (digitFunction m d u k).val)+(∑ k, (digitFunction b d v k).val) ≤ D →
      (a (lowCode (m*b) d (zipDigit m b d u v)):ZMod T)=
        Sparse.coefficient (ZMod T) m b P (digitFunction m d u) (digitFunction b d v))
    (i : DigitBox m d) (y : DigitBox b d) :
    (tensorValue T b b (powerTable T b) d
      (gathered true m b d D (((b-3)*d)/2) (lowCode m d i) a) (lowCode b d y):ZMod T)=
        Weighted.W P (digitFunction m d i) (digitFunction b d y) := by
  rw [tensorValue_evaluation hb]
  unfold Weighted.W Weighted.monomial
  have hset : (Weighted.lowSet b d)ᶜ=univ.filter (fun j : Fin d → Fin b => ((b-3)*d)/2 < Weighted.degree j) := by
    ext j
    simp only [mem_compl,Weighted.lowSet,mem_filter,mem_univ,true_and]
    omega
  rw [hset,sum_filter,← (digitFunctionEquiv b d).sum_comp]
  apply sum_congr rfl
  intro v _
  change _=if ((b-3)*d)/2 < Weighted.degree (digitFunction b d v) then
    Sparse.coefficient (ZMod T) m b P (digitFunction m d i) (digitFunction b d v)*_ else 0
  rw [gathered_W]
  unfold Weighted.degree
  by_cases hdeg : (∑ k, (digitFunction m d i k).val)+(∑ k, (digitFunction b d v k).val) ≤ D
  · by_cases htail : ((b-3)*d)/2 < ∑ k, (digitFunction b d v k).val
    · simp only [hdeg,htail,and_self,ite_true,ha i v hdeg]
      rfl
    · simp [htail]
  · rw [Sparse.coefficient_support (ZMod T) P hP _ _ (by omega)]
    simp [hdeg]
end
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured
open Command

def copyStep := straight [
  .binary 4 .add (.register 0) (.register 3),.load 5 (.register 4),
  .binary 6 .add (.register 1) (.register 3),.store (.register 6) (.register 5)]

theorem copyStep_correct {w A P n i : ℕ} (s : Data) (f : ℕ → ℕ)
    (hi : i<n) (hA : A+n<wordModulus w) (hP : P+n<wordModulus w)
    (h0 : s.registers 0=A) (h1 : s.registers 1=P) (h3 : s.registers 3=i)
    (hf : f i<wordModulus w) (hm : s.memory (A+i)=some (f i)) :
    ∃ t, Eval w copyStep s 4 t ∧
      (∀ r, r≤3 ∨ 7≤r → t.registers r=s.registers r) ∧
      t.memory=Function.update s.memory (P+i) (some (f i)) := by
  let u:=put (put (put s 4 (A+i)) 5 (f i)) 6 (P+i)
  let t : Data := {u with memory:=Function.update s.memory (P+i) (some (f i))}
  refine ⟨t,?_,?_,rfl⟩
  · apply straight_correct
    simp [execStraight,Atom.eval,evalBinOp,operand_register,h0,h1,h3,put,u,t,
      Nat.mod_eq_of_lt hf,Nat.mod_eq_of_lt (show A<wordModulus w by omega),
      Nat.mod_eq_of_lt (show i<wordModulus w by omega),
      Nat.mod_eq_of_lt (show A+i<wordModulus w by omega),Nat.mod_eq_of_lt (show P+i<wordModulus w by omega),hm]
  · intro r hr
    simp only [t,u,put,Function.update_of_ne (by omega : r≠6),
      Function.update_of_ne (by omega : r≠5),Function.update_of_ne (by omega : r≠4)]

def copyPass : Command := .seq (.atom (.assign 3 (.literal 0))) (indexedLoop 3 2 copyStep)

theorem copyPass_correct {w A P n : ℕ} (s : Data) (f : ℕ → ℕ)
    (hA : A+n<wordModulus w) (hP : P+n+1<wordModulus w)
    (hdisj : A+n≤P ∨ P+n≤A)
    (h0 : s.registers 0=A) (h1 : s.registers 1=P) (h2 : s.registers 2=n)
    (hf : ∀ i, i<n → f i<wordModulus w)
    (hm : ∀ i, i<n → s.memory (A+i)=some (f i)) :
    ∃ cost t, Eval w copyPass s cost t ∧ cost≤7*n+2 ∧
      (∀ r, r≤2 ∨ 7≤r → t.registers r=s.registers r) ∧
      t.memory=written s P f n := by
  let s0:=put s 3 0
  have e0 : Eval w (.atom (.assign 3 (.literal 0))) s 1 s0 := by
    simpa [operand_literal] using eval_assign (w:=w) s 3 (.literal 0)
  obtain ⟨cost,t,he,hc,hr,hi,ht⟩ := indexedLoop_correct (w:=w) (n:=n) (index:=3) (bound:=2) (base:=P) (K:=4)
    (by omega) (by decide) copyStep s s0 f (fun r => r≤2 ∨ 7≤r) (by decide) (by omega)
    (by simpa [s0,put] using h2) (by simp [s0,put]) rfl (by
      intro i u h_i hu hindex hmem
      have hsource : u.memory (A+i)=some (f i) := by
        rw [hmem,written_outside (by omega : A+i<P ∨ P+i≤A+i)]
        exact hm i h_i
      obtain ⟨v,ev,hv,hvm⟩ := copyStep_correct (w:=w) (A:=A) (P:=P) (n:=n) u f h_i hA (by omega)
        (by simpa [s0,put] using (hu 0 (by omega)).trans (by simpa [s0,put] using h0))
        (by simpa [s0,put] using (hu 1 (by omega)).trans (by simpa [s0,put] using h1))
        hindex (hf i h_i) hsource
      exact ⟨4,v,ev,le_rfl,fun r h => hv r (by omega),hvm⟩)
  refine ⟨1+cost,t,Eval.seq e0 he,by omega,?_,ht⟩
  intro r h
  rw [hr r h]
  simp only [s0,put,Function.update_of_ne (by omega : r≠3)]

end DeterministicThreeSum.Structured
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def batchBase (tail : Bool) (m b q : ℕ) : ℕ :=
  max 26 ((evaluateRow tail m b q).writes.sup id+1)

lemma batchBase_ge (tail : Bool) (m b q : ℕ) : 26≤batchBase tail m b q := le_max_left ..
lemma batchBase_gt (tail : Bool) (m b q : ℕ) :
    (evaluateRow tail m b q).writes.sup id<batchBase tail m b q :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ..)

def batchValues (i rows nodes dest N S D H d stride T C P V : ℕ) (q : ℕ) (r : ℕ) : ℕ :=
  match r with
  | 0=>i | 1=>rows | 2=>nodes | 3=>dest | 4=>N | 5=>S | 6=>D | 7=>H
  | 8=>d | 9=>stride | 10=>q*stride | 11=>T | 12=>C | 13=>P | 14=>V
  | 15=>(banks d V P).2 | _=>0

def batchSources (k : ℕ) (r : ℕ) : Operand :=
  match r with
  | 13=>.register (k+4) | 15=>.register (k+13) | 16=>.register (k+5)
  | 17=>.register (k+6) | 18=>.register (k+7) | 20=>.register (k+8)
  | 21=>.register (k+9) | 22=>.register (k+10) | 23=>.register (k+11)
  | 24=>.register (k+12) | 25=>.register (k+14) | _=>.literal 0

def batchLowValues (N S D H d stride T C P V q : ℕ) (r : ℕ) : ℕ :=
  match r with
  | 13=>N | 15=>P | 16=>S | 17=>D | 18=>H | 20=>d | 21=>stride
  | 22=>q*stride | 23=>T | 24=>C | 25=>V | _=>0

def batchSetup (k : ℕ) : Command := copyPrefix (batchSources k) 26

lemma batchSetup_correct {w k i rows nodes dest N S D H d stride T C P V q : ℕ}
    (s : Data) (hk : 26≤k)
    (hb : ∀ r, r<16 → batchValues i rows nodes dest N S D H d stride T C P V q r<wordModulus w)
    (hr : ∀ r, r<16 → s.registers (k+r)=batchValues i rows nodes dest N S D H d stride T C P V q r) :
    Eval w (batchSetup k) s 26 (patched s 26 (batchLowValues N S D H d stride T C P V q)) := by
  apply copyPrefix_correct
  · intro j hj r hr'
    interval_cases j <;> simp [batchSources] at hr' <;> subst r <;> omega
  · intro j hj
    interval_cases j <;> simp [batchSources,batchLowValues,operand_literal,operand_register,
      hr,batchValues]
    · exact Nat.mod_eq_of_lt (hb 4 (by decide))
    · exact Nat.mod_eq_of_lt (hb 13 (by decide))
    · exact Nat.mod_eq_of_lt (hb 5 (by decide))
    · exact Nat.mod_eq_of_lt (hb 6 (by decide))
    · exact Nat.mod_eq_of_lt (hb 7 (by decide))
    · exact Nat.mod_eq_of_lt (hb 8 (by decide))
    · exact Nat.mod_eq_of_lt (hb 9 (by decide))
    · exact Nat.mod_eq_of_lt (hb 10 (by decide))
    · exact Nat.mod_eq_of_lt (hb 11 (by decide))
    · exact Nat.mod_eq_of_lt (hb 12 (by decide))
    · exact Nat.mod_eq_of_lt (hb 14 (by decide))

def loadKey (k : ℕ) : Command := straight [
  .binary 0 .mul (.register k) (.literal 2),
  .binary 0 .add (.register 0) (.register (k+2)),
  .load 14 (.register 0)]

lemma loadKey_correct {w k nodes i key : ℕ} (s : Data) (hk : 26≤k)
    (haddr : nodes+2*i<wordModulus w) (_hkey : key<wordModulus w) (hW : 2<wordModulus w)
    (h0 : s.registers k=i) (h2 : s.registers (k+2)=nodes)
    (hm : s.memory (nodes+2*i)=some key) :
    Eval w (loadKey k) s 3 (put (put s 0 (nodes+2*i)) 14 key) := by
  have hi : i<wordModulus w := by omega
  apply straight_correct
  simp [execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,h0,h2,
    show k≠0 by omega,
    Nat.mod_eq_of_lt (by omega : i*2<wordModulus w),Nat.mod_eq_of_lt hW,Nat.mod_eq_of_lt hi,
    Nat.mul_comm,Nat.add_comm,Function.update_idem,
    Nat.mod_eq_of_lt (show nodes+i*2<wordModulus w by nlinarith only [haddr]),
    show s.memory (nodes+i*2)=some key by simpa only [Nat.mul_comm] using hm]

def rowCopySetup (k : ℕ) : Command := straight [
  .binary 1 .mul (.register k) (.register (k+4)),
  .binary 1 .add (.register 1) (.register (k+3)),
  .assign 0 (.register (k+15)), .assign 2 (.register (k+4))]

lemma rowCopySetup_correct {w k i N dest A : ℕ} (s : Data) (hk : 26≤k)
    (haddr : dest+i*N<wordModulus w) (hi : i<wordModulus w)
    (hN : N<wordModulus w) (hA : A<wordModulus w)
    (h0 : s.registers k=i) (h3 : s.registers (k+3)=dest)
    (h4 : s.registers (k+4)=N) (h15 : s.registers (k+15)=A) :
    Eval w (rowCopySetup k) s 4 (put (put (put s 1 (dest+i*N)) 0 A) 2 N) := by
  apply straight_correct
  simp [execStraight,Atom.eval,operand_register,evalBinOp,put,
    h0,h3,h4,h15,show k+3≠1 by omega,show k+15≠1 by omega,
    show k+4≠1 by omega,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hN,
    Nat.mod_eq_of_lt hA,Nat.mod_eq_of_lt (by omega : i*N<wordModulus w),
    Nat.add_comm,Nat.mod_eq_of_lt haddr,
    Function.update_idem]

end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def storeRow (tail : Bool) (m b q k : ℕ) : Command :=
  .seq (evaluateRow tail m b q) (.seq (rowCopySetup k) copyPass)

theorem storeRow_correct {w T m b q d D H key P S V C L k index dest : ℕ}
    (tail : Bool) (s : Data) (x c : ℕ → ℕ)
    (hm : 1 < m) (hb : 1 < b) (hq : 1 < q) (hR : m*b < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hL : q^d ≤ L) (hLw : L*q+L+3 < wordModulus w)
    (hP : P+L+1 < wordModulus w) (hV : V+L+1 < wordModulus w)
    (hS : S+(m*b)^d < wordModulus w) (hC : C+q*q < wordModulus w)
    (hSP : P+L ≤ S ∨ S+(m*b)^d ≤ P)
    (hVP : P+L ≤ V ∨ V+L ≤ P)
    (hCP : C+q*q ≤ P ∨ P+L ≤ C) (hCV : C+q*q ≤ V ∨ V+L ≤ C)
    (hl : ∀ i, i < q^d → leftIndex tail key i < m^d)
    (hr : ∀ i, i < q^d → rightIndex tail key i < b^d)
    (h13 : s.registers 13=q^d) (h14 : s.registers 14=key)
    (h15 : s.registers 15=P) (h16 : s.registers 16=S)
    (h17 : s.registers 17=D) (h18 : s.registers 18=H) (h20 : s.registers 20=d)
    (h21 : s.registers 21=tensorStride q d) (h22 : s.registers 22=q*tensorStride q d)
    (h23 : s.registers 23=T) (h24 : s.registers 24=C) (h25 : s.registers 25=V)
    (hxw : ∀ i, i < q^d → x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)) < T)
    (hx : ∀ i, i < q^d →
      DigitSum.value m d (leftIndex tail key i)+DigitSum.value b d (rightIndex tail key i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail key i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))=
        some (x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))))
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (hk : 26≤k) (hkw : (evaluateRow tail m b q).writes.sup id<k)
    (hindex : index<wordModulus w) (hDest : dest+(index+1)*q^d+1<wordModulus w)
    (hDP : P+L≤dest ∨ dest+(index+1)*q^d≤P)
    (hDV : V+L≤dest ∨ dest+(index+1)*q^d≤V)
    (hk0 : s.registers k=index) (hk3 : s.registers (k+3)=dest)
    (hk4 : s.registers (k+4)=q^d) (hk15 : s.registers (k+15)=(banks d V P).2) :
    ∃ cost z, Eval w (storeRow tail m b q k) s cost z ∧
      cost ≤ (14*d+27)*q^d+(((row q q).cost+5)*L+11)*d+17 ∧
      (∀ j, j<q^d → z.memory (dest+index*q^d+j)=some
        (tensorValue T q q c d (gathered tail m b d D H key x) j)) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<V ∨ V+L≤a) →
        (a<dest+index*q^d ∨ dest+(index+1)*q^d≤a) → z.memory a=s.memory a) ∧
      (∀ r, z.registers (k+r)=s.registers (k+r)) := by
  obtain ⟨a,u,eu,ha,hum,huf⟩:=evaluateRow_correct tail s x c hm hb hq hR hT hadd hmul
    hd hD hH hvol hsum hL hLw hP hV hS hC hSP hVP hCP hCV hl hr
    h13 h14 h15 h16 h17 h18 h20 h21 h22 h23 h24 h25 hxw hx hc
  have hur (r : ℕ) : u.registers (k+r)=s.registers (k+r) := protected_frame eu hkw r
  let A:=(banks d V P).2
  have hA : A+q^d<wordModulus w := by
    dsimp [A,banks]; split_ifs <;> dsimp <;> omega
  have hsplit : (index+1)*q^d=index*q^d+q^d := by ring
  rw [hsplit] at hDest hDP hDV
  have hdis : A+q^d≤dest+index*q^d ∨ dest+index*q^d+q^d≤A := by
    dsimp [A,banks]; split_ifs <;> dsimp <;> omega
  have ep:=rowCopySetup_correct u hk (by omega) hindex (by omega) (by omega : A<wordModulus w)
    (by simpa only [Nat.add_zero] using (hur 0).trans hk0)
    ((hur 3).trans hk3) ((hur 4).trans hk4) ((hur 15).trans hk15)
  let v:=put (put (put u 1 (dest+index*q^d)) 0 A) 2 (q^d)
  obtain ⟨b,z,ez,hb',hzr,hzm⟩:=copyPass_correct v
    (tensorValue T q q c d (gathered tail m b d D H key x)) hA
    (by omega) hdis (by simp [v,put]) (by simp [v,put]) (by simp [v,put])
    (fun j hj => (hum j hj).2.trans (by omega : T<wordModulus w))
    (fun j hj => (hum j hj).1)
  refine ⟨a+(4+b),z,Eval.seq eu (Eval.seq ep ez),?_,?_,?_,?_⟩
  · calc a+(4+b) ≤ ((14*d+20)*q^d+(((row q q).cost+5)*L+11)*d+11)+(4+(7*q^d+2)) := by omega
         _ = _ := by ring
  · intro j hj
    rw [hzm]
    simp [written,hj]
  · intro j hjP hjV hjD
    rw [hsplit] at hjD
    rw [hzm,written_outside (by omega)]
    exact huf j hjP hjV
  · intro r
    rw [hzr (k+r) (by omega)]
    simp only [v,put,Function.update_of_ne (show k+r≠2 by omega),
      Function.update_of_ne (show k+r≠0 by omega),Function.update_of_ne (show k+r≠1 by omega)]
    exact hur r
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def prepareRow (k : ℕ) : Command := .seq (batchSetup k) (loadKey k)

def prepared (s : Data) (nodes i key N S D H d stride T C P V q : ℕ) : Data :=
  put (put (patched s 26 (batchLowValues N S D H d stride T C P V q)) 0 (nodes+2*i)) 14 key

lemma prepareRow_correct {w k i rows nodes dest N S D H d stride T C P V q key : ℕ}
    (s : Data) (hk : 26≤k) (hW : 2<wordModulus w)
    (hb : ∀ r, r<16 → batchValues i rows nodes dest N S D H d stride T C P V q r<wordModulus w)
    (hr : ∀ r, r<16 → s.registers (k+r)=batchValues i rows nodes dest N S D H d stride T C P V q r)
    (haddr : nodes+2*i<wordModulus w) (hkey : key<wordModulus w)
    (hm : s.memory (nodes+2*i)=some key) :
    Eval w (prepareRow k) s 29 (prepared s nodes i key N S D H d stride T C P V q) := by
  have ep:=batchSetup_correct s hk hb hr
  have hk0 : (patched s 26 (batchLowValues N S D H d stride T C P V q)).registers k=i := by
    simp only [patched,ite_eq_right (by omega : ¬k<26)]
    simpa [batchValues] using hr 0 (by decide)
  have hk2 : (patched s 26 (batchLowValues N S D H d stride T C P V q)).registers (k+2)=nodes := by
    simp only [patched,ite_eq_right (by omega : ¬k+2<26)]
    simpa [batchValues] using hr 2 (by decide)
  have el:=loadKey_correct (patched s 26 (batchLowValues N S D H d stride T C P V q))
    hk haddr hkey hW hk0 hk2 hm
  exact Eval.seq ep el

lemma prepared_low (s : Data) (nodes i key N S D H d stride T C P V q r : ℕ)
    (hr : 13≤r) (hr' : r<26) :
    (prepared s nodes i key N S D H d stride T C P V q).registers r=
      if r=14 then key else batchLowValues N S D H d stride T C P V q r := by
  by_cases h14 : r=14
  · subst r; simp [prepared,put]
  · simp [prepared,put,h14,show r≠0 by omega,patched,hr']

lemma prepared_frame (s : Data) (nodes i key N S D H d stride T C P V q k r : ℕ)
    (hk : 26≤k) :
    (prepared s nodes i key N S D H d stride T C P V q).registers (k+r)=s.registers (k+r) := by
  simp only [prepared,put,Function.update_of_ne (show k+r≠14 by omega),
    Function.update_of_ne (show k+r≠0 by omega),patched,ite_eq_right (show ¬k+r<26 by omega)]
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def batchBody (tail : Bool) (m b q k : ℕ) : Command :=
  .seq (prepareRow k) (storeRow tail m b q k)

lemma outside_separated {P L S n a : ℕ} (h : P+L ≤ S ∨ S+n ≤ P)
    (ha : S ≤ a) (ha' : a < S+n) : a < P ∨ P+L ≤ a := by omega

lemma batchValues_nonzero (i j rows nodes dest N S D H d stride T C P V q r : ℕ)
    (hr : 0 < r) :
    batchValues i rows nodes dest N S D H d stride T C P V q r=
    batchValues j rows nodes dest N S D H d stride T C P V q r := by
  unfold batchValues
  split <;> simp_all

lemma batchValues_bound {w i rows nodes dest N S D H d stride T C P V q : ℕ}
    (hi : i < wordModulus w) (hrows : rows < wordModulus w)
    (hnodes : nodes < wordModulus w) (hdest : dest < wordModulus w)
    (hN : N < wordModulus w) (hS : S < wordModulus w)
    (hD : D < wordModulus w) (hH : H < wordModulus w) (hd : d < wordModulus w)
    (hstride : stride < wordModulus w) (hcount : q*stride < wordModulus w)
    (hT : T < wordModulus w) (hC : C < wordModulus w)
    (hP : P < wordModulus w) (hV : V < wordModulus w)
    (hbank : (banks d V P).2 < wordModulus w) :
    ∀ r, r < 16 → batchValues i rows nodes dest N S D H d stride T C P V q r < wordModulus w := by
  intro r hr
  interval_cases r <;> simp only [batchValues] <;> assumption

theorem batchBody_correct {w T m b q d D H key P S V C L k index rows nodes dest : ℕ}
    (tail : Bool) (s : Data) (x c : ℕ → ℕ)
    (hm : 1 < m) (hb : 1 < b) (hq : 1 < q) (hR : m*b < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hL : q^d ≤ L) (hLw : L*q+L+3 < wordModulus w)
    (hP : P+L+1 < wordModulus w) (hV : V+L+1 < wordModulus w)
    (hS : S+(m*b)^d < wordModulus w) (hC : C+q*q < wordModulus w)
    (hSP : P+L ≤ S ∨ S+(m*b)^d ≤ P) (hVP : P+L ≤ V ∨ V+L ≤ P)
    (hCP : C+q*q ≤ P ∨ P+L ≤ C) (hCV : C+q*q ≤ V ∨ V+L ≤ C)
    (hl : ∀ i, i < q^d → leftIndex tail key i < m^d)
    (hr : ∀ i, i < q^d → rightIndex tail key i < b^d)
    (hxw : ∀ i, i < q^d → x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)) < T)
    (hx : ∀ i, i < q^d →
      DigitSum.value m d (leftIndex tail key i)+DigitSum.value b d (rightIndex tail key i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail key i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))=
        some (x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))))
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (hk : 26 ≤ k) (hkw : (evaluateRow tail m b q).writes.sup id < k)
    (hDest : dest+(index+1)*q^d+1 < wordModulus w)
    (hDP : P+L ≤ dest ∨ dest+(index+1)*q^d ≤ P)
    (hDV : V+L ≤ dest ∨ dest+(index+1)*q^d ≤ V)
    (hbctx : ∀ r, r < 16 → batchValues index rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r < wordModulus w)
    (hctx : ∀ r, r < 16 → s.registers (k+r)=batchValues index rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r)
    (haddr : nodes+2*index < wordModulus w) (hkey : key < wordModulus w)
    (hmem : s.memory (nodes+2*index)=some key) :
    ∃ cost z, Eval w (batchBody tail m b q k) s cost z ∧
      cost ≤ (14*d+27)*q^d+(((row q q).cost+5)*L+11)*d+46 ∧
      (∀ j, j < q^d → z.memory (dest+index*q^d+j)=some
        (tensorValue T q q c d (gathered tail m b d D H key x) j)) ∧
      (∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) →
        (a < dest+index*q^d ∨ dest+(index+1)*q^d ≤ a) → z.memory a=s.memory a) ∧
      (∀ r, z.registers (k+r)=s.registers (k+r)) := by
  have ep:=prepareRow_correct s hk (by omega) hbctx hctx haddr hkey hmem
  let u:=prepared s nodes index key (q^d) S D H d (tensorStride q d) T C P V q
  have ul (r : ℕ) (hr13 : 13 ≤ r) (hr26 : r < 26) :=
    prepared_low s nodes index key (q^d) S D H d (tensorStride q d) T C P V q r hr13 hr26
  have uf (r : ℕ) : u.registers (k+r)=s.registers (k+r) :=
    prepared_frame s nodes index key (q^d) S D H d (tensorStride q d) T C P V q k r hk
  obtain ⟨a,z,ez,ha,hmz,hfz,hrz⟩:=storeRow_correct tail u x c hm hb hq hR hT hadd hmul
    hd hD hH hvol hsum hL hLw hP hV hS hC hSP hVP hCP hCV hl hr
    (by simpa [batchLowValues] using ul 13 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 14 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 15 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 16 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 17 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 18 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 20 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 21 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 22 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 23 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 24 (by decide) (by decide))
    (by simpa [batchLowValues] using ul 25 (by decide) (by decide))
    hxw hx hc hk hkw (by simpa [batchValues] using hbctx 0 (by decide)) hDest hDP hDV
    (by simpa only [Nat.add_zero] using (uf 0).trans (by simpa [batchValues] using hctx 0 (by decide)))
    ((uf 3).trans (by simpa [batchValues] using hctx 3 (by decide)))
    ((uf 4).trans (by simpa [batchValues] using hctx 4 (by decide)))
    ((uf 15).trans (by simpa [batchValues] using hctx 15 (by decide)))
  refine ⟨29+a,z,Eval.seq ep ez,by omega,hmz,hfz,?_⟩
  exact fun r => (hrz r).trans (uf r)
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

lemma batchCtx_bounds {w i rows nodes dest T q d D H S C P V L : ℕ}
    (hiq : i ≤ rows) (hrows : rows+1 < wordModulus w)
    (hnodes : nodes+2*rows < wordModulus w) (hdest : dest+rows*q^d+1 < wordModulus w)
    (hq : 1 < q) (hadd : 2*T < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hL : q^d ≤ L) (_hLw : L*q+L+3 < wordModulus w)
    (hP : P+L+1 < wordModulus w) (hV : V+L+1 < wordModulus w)
    (hS : S < wordModulus w) (hC : C < wordModulus w) :
    ∀ r, r < 16 → batchValues i rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r < wordModulus w := by
  have hstr : tensorStride q d < wordModulus w := (NewtonPass.tensorStride_le hq d).trans_lt (by omega)
  have hcount : q*tensorStride q d < wordModulus w := by
    have hh:=NewtonPass.initialCount_le (A:=1) hq d
    simp only [one_mul] at hh
    omega
  have hbank : (banks d V P).2 < wordModulus w := by
    dsimp [banks]; split_ifs <;> dsimp <;> omega
  exact batchValues_bound (by omega) (by omega) (by omega) (by omega)
    (by omega) hS hD hH hd hstr hcount (by omega) hC (by omega) (by omega) hbank

lemma readonly_cache {t s : Data} {P V L dest N i rows R B a : ℕ}
    (hf : ∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) →
      (a < dest ∨ dest+i*N ≤ a) → t.memory a=s.memory a)
    (hi : i ≤ rows) (hp : P+L ≤ R ∨ R+B ≤ P) (hv : V+L ≤ R ∨ R+B ≤ V)
    (hd : dest+rows*N ≤ R ∨ R+B ≤ dest) (ha : R ≤ a) (ha' : a < R+B) :
    t.memory a=s.memory a := by
  apply hf a (outside_separated hp ha ha') (outside_separated hv ha ha')
  have hh:=Nat.mul_le_mul_right N hi
  omega

end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def batchCommand (tail : Bool) (m b q : ℕ) : Command :=
  indexedLoop (batchBase tail m b q) (batchBase tail m b q+1)
    (batchBody tail m b q (batchBase tail m b q))

theorem batchCommand_correct {w T m b q d D H P S V C L nodes dest rows : ℕ}
    (tail : Bool) (s : Data) (x c keys : ℕ → ℕ)
    (hm : 1  <  m) (hb : 1  <  b) (hq : 1  <  q) (hR : m*b < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hL : q^d ≤ L) (hLw : L*q+L+3 < wordModulus w)
    (hP : P+L+1 < wordModulus w) (hV : V+L+1 < wordModulus w)
    (hS : S+(m*b)^d < wordModulus w) (hC : C+q*q < wordModulus w)
    (hSP : P+L ≤ S ∨ S+(m*b)^d ≤ P) (hSV : V+L ≤ S ∨ S+(m*b)^d ≤ V)
    (hVP : P+L ≤ V ∨ V+L ≤ P)
    (hCP : C+q*q ≤ P ∨ P+L ≤ C) (hCV : C+q*q ≤ V ∨ V+L ≤ C)
    (hrows : rows+1 < wordModulus w) (hnodes : nodes+2*rows < wordModulus w)
    (hdest : dest+rows*q^d+1 < wordModulus w)
    (hDP : P+L ≤ dest ∨ dest+rows*q^d ≤ P) (hDV : V+L ≤ dest ∨ dest+rows*q^d ≤ V)
    (hDS : dest+rows*q^d ≤ S ∨ S+(m*b)^d ≤ dest)
    (hDC : dest+rows*q^d ≤ C ∨ C+q*q ≤ dest)
    (hNP : P+L ≤ nodes ∨ nodes+2*rows ≤ P) (hNV : V+L ≤ nodes ∨ nodes+2*rows ≤ V)
    (hND : dest+rows*q^d ≤ nodes ∨ nodes+2*rows ≤ dest)
    (hkeys : ∀ j, j < rows → keys j < wordModulus w)
    (hnmem : ∀ j, j < rows → s.memory (nodes+2*j)=some (keys j))
    (hl : ∀ j, j < rows → ∀ i, i < q^d → leftIndex tail (keys j) i < m^d)
    (hr : ∀ j, j < rows → ∀ i, i < q^d → rightIndex tail (keys j) i < b^d)
    (hxw : ∀ j, j < rows → ∀ i, i < q^d →
      x (ZipIndex.value m b d (leftIndex tail (keys j) i) (rightIndex tail (keys j) i)) < T)
    (hx : ∀ j, j < rows → ∀ i, i < q^d →
      DigitSum.value m d (leftIndex tail (keys j) i)+DigitSum.value b d (rightIndex tail (keys j) i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail (keys j) i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail (keys j) i) (rightIndex tail (keys j) i))=
        some (x (ZipIndex.value m b d (leftIndex tail (keys j) i) (rightIndex tail (keys j) i))))
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (hregs : ∀ r, r < 16 → s.registers (batchBase tail m b q+r)=
      batchValues 0 rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r) :
    ∃ cost z, Eval w (batchCommand tail m b q) s cost z ∧
      cost ≤ ((14*d+27)*q^d+(((row q q).cost+5)*L+11)*d+49)*rows+1 ∧
      (∀ j, j < rows → ∀ v, v < q^d → z.memory (dest+j*q^d+v)=some
        (tensorValue T q q c d (gathered tail m b d D H (keys j) x) v)) ∧
      (∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) →
        (a < dest ∨ dest+rows*q^d ≤ a) → z.memory a=s.memory a) ∧
      (∀ r, 0 < r → z.registers (batchBase tail m b q+r)=s.registers (batchBase tail m b q+r)) := by
  let k:=batchBase tail m b q
  let val : ℕ → ℕ → ℕ := fun j v => tensorValue T q q c d (gathered tail m b d D H (keys j) x) v
  let B:=(14*d+27)*(q^d)+(((row q q).cost+5)*L+11)*d+47
  have hk : 26 ≤ k := batchBase_ge ..
  have hkw : (evaluateRow tail m b q).writes.sup id < k := batchBase_gt ..
  let Inv : ℕ → Data → Prop := fun i t =>
    t.registers k=i ∧
    (∀ r, 0 < r → t.registers (k+r)=s.registers (k+r)) ∧
    (∀ j, j < i → ∀ v, v < (q^d) → t.memory (dest+j*(q^d)+v)=some (val j v)) ∧
    (∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) →
      (a < dest ∨ dest+i*(q^d) ≤ a) → t.memory a=s.memory a)
  have hbctx : ∀ i, i ≤ rows → ∀ r, r < 16 →
      batchValues i rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r < wordModulus w := by
    intro i hi
    exact batchCtx_bounds hi hrows hnodes hdest hq hadd hd hD hH hL hLw hP hV (by omega) (by omega)
  have hctx : ∀ i t, Inv i t → ∀ r, r < 16 → t.registers (k+r)=
      batchValues i rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r := by
    intro i t ht r hrr
    rcases r with _|r
    · simpa only [Nat.add_zero,batchValues] using ht.1
    · rw [ht.2.1 (r+1) (by omega),hregs (r+1) hrr]
      exact batchValues_nonzero 0 i rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q (r+1) (by omega)
  have hyes : ∀ i t, i < rows → Inv i t → test w t .lt (.register k) (.register (k+1))=true := by
    intro i t hi ht
    have hbound : t.registers (k+1)=rows := by simpa [batchValues] using hctx i t ht 1 (by decide)
    simp [test,operand_register,evalTest,ht.1,hbound,
      Nat.mod_eq_of_lt (by omega : i < wordModulus w),Nat.mod_eq_of_lt (by omega : rows < wordModulus w),hi]
  have hno : ∀ t, Inv rows t → test w t .lt (.register k) (.register (k+1))=false := by
    intro t ht
    have hbound : t.registers (k+1)=rows := by simpa [batchValues] using hctx rows t ht 1 (by decide)
    simp [test,operand_register,evalTest,ht.1,hbound]
  have hstep : ∀ i t, i < rows → Inv i t → ∃ cost z,
      Eval w (.seq (batchBody tail m b q k) (.atom (.binary k .add (.register k) (.literal 1)))) t cost z ∧
      cost ≤ B ∧ Inv (i+1) z := by
    intro i t hi ht
    have himul : i*(q^d) ≤ rows*(q^d) := Nat.mul_le_mul_right (q^d) (by omega : i ≤ rows)
    have hipmul : (i+1)*(q^d) ≤ rows*(q^d) := Nat.mul_le_mul_right (q^d) hi
    have hkeymem : t.memory (nodes+2*i)=some (keys i) := by
      rw [readonly_cache ht.2.2.2 hi.le hNP hNV hND (Nat.le_add_right nodes (2*i))
        (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)) nodes)]
      exact hnmem i hi
    have thm : ∀ j, j < q^d →
        DigitSum.value m d (leftIndex tail (keys i) j)+DigitSum.value b d (rightIndex tail (keys i) j) ≤ D →
        TailOK tail H (DigitSum.value b d (rightIndex tail (keys i) j)) →
        t.memory (S+ZipIndex.value m b d (leftIndex tail (keys i) j) (rightIndex tail (keys i) j))=
          some (x (ZipIndex.value m b d (leftIndex tail (keys i) j) (rightIndex tail (keys i) j))) := by
      intro j hj hdeg htail
      have hv:=ZipIndex.value_lt (by omega : 0 < m) (by omega : 0 < b) d
        (leftIndex tail (keys i) j) (rightIndex tail (keys i) j)
      rw [readonly_cache ht.2.2.2 hi.le hSP hSV hDS (Nat.le_add_right S _)
        (Nat.add_lt_add_left hv S)]
      exact hx i hi j hj hdeg htail
    have thc : ∀ j, j < q*q → t.memory (C+j)=some (c j) ∧ c j < T := by
      intro j hj
      rw [readonly_cache ht.2.2.2 hi.le hCP.symm hCV.symm hDC (Nat.le_add_right C j)
        (Nat.add_lt_add_left hj C)]
      exact hc j hj
    obtain ⟨a,v,ev,ha,hvm,hvf,hvr⟩:=batchBody_correct tail t x c hm hb hq hR hT hadd hmul
      hd hD hH hvol hsum hL hLw hP hV hS hC hSP hVP hCP hCV (hl i hi) (hr i hi)
      (hxw i hi) thm thc hk hkw
      (by omega : dest+(i+1)*q^d+1 < wordModulus w)
      (by omega : P+L ≤ dest ∨ dest+(i+1)*q^d ≤ P)
      (by omega : V+L ≤ dest ∨ dest+(i+1)*q^d ≤ V)
      (hbctx i hi.le) (hctx i t ht) (by omega) (hkeys i hi) hkeymem
    have hvi : v.registers k=i := by simpa only [Nat.add_zero] using (hvr 0).trans (by simpa using ht.1)
    have ei:=eval_increment (w:=w) (s:=v) (r:=k) (by rw [hvi]; omega)
    rw [hvi] at ei
    refine ⟨a+1,put v k (i+1),Eval.seq ev ei,?_,?_,?_,?_,?_⟩
    · dsimp [B]; omega
    · simp [put]
    · intro r hr'
      rw [show (put v k (i+1)).registers (k+r)=v.registers (k+r) by simp only [put, Function.update_of_ne (show k+r≠k by omega)]]
      exact (hvr r).trans (ht.2.1 r hr')
    · intro j hj z hz
      change v.memory _=_
      by_cases hji : j=i
      · subst j; exact hvm z hz
      · have hjmul : (j+1)*(q^d) ≤ i*(q^d) := Nat.mul_le_mul_right (q^d) (by omega : j+1 ≤ i)
        have hjN : j*(q^d)+z <  i*(q^d) := by nlinarith only [hjmul,hz]
        rw [hvf _ (by omega) (by omega) (by omega)]
        exact ht.2.2.1 j (by omega) z hz
    · intro a haP haV haD
      change v.memory a=s.memory a
      have hiN : i*(q^d) ≤ (i+1)*(q^d) := Nat.mul_le_mul_right (q^d) (by omega : i ≤ i+1)
      rw [hvf a haP haV (by omega)]
      exact ht.2.2.2 a haP haV (by omega)
  have hs : Inv 0 s := by
    refine ⟨?_,fun _ _=>rfl,by simp,fun _ _ _ _=>rfl⟩
    simpa [batchValues] using hregs 0 (by decide)
  obtain ⟨cost,z,ez,hcost,hz⟩:=bounded_loop Inv hyes hno hstep (i:=0) (by omega) hs
  refine ⟨cost,z,ez,?_,hz.2.2.1,hz.2.2.2,hz.2.1⟩
  simpa only [B,Nat.sub_zero,Nat.add_assoc] using hcost
end DeterministicThreeSum.Structured.Indexed.Cache

end OAI
