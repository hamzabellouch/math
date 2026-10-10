import Mathlib
import OAI.Computability.DeterministicSum.PaddedMaps

namespace OAI

/-! Uniform downward matrix recursion and address-capacity invariants. -/

namespace DeterministicThreeSum.Structured.Indexed.MatrixDown
open Command DeterministicThreeSum.Rectangular Axis MatrixLayout

def update (Q k r : ℕ) : Command := straight [
  .assign 8 (.register 3), .assign 3 (.register 4), .assign 4 (.register 8),
  .assign 7 (.register 1), .assign 9 (.register 6),
  .binary 6 .quot (.register 6) (.literal Q),
  .binary 8 .quot (.register 1) (.register 9),
  .binary 8 .add (.register 8) (.literal (k-1)),
  .binary 8 .quot (.register 8) (.literal k),
  .binary 1 .mul (.register 8) (.literal r),
  .binary 1 .mul (.register 1) (.register 6), .assign 0 (.literal 0)]

def updated (s : Data) (Q k r P S B n : ℕ) : Data :=
  put (put (put (put (put (put (put (put (put (put (put (put s 8 P) 3 S) 4 P)
    7 (n*B)) 9 B) 6 (B/Q)) 8 n) 8 (n+(k-1))) 8 ((n+(k-1))/k))
      1 (((n+(k-1))/k)*r)) 1 (((n+(k-1))/k)*r*(B/Q))) 0 0

lemma ceil_eq {k : ℕ} (hk : 0<k) (n : ℕ) : (n+(k-1))/k=batchCount n k := by
  rw [batchCount,Nat.ceilDiv_eq_add_pred_div]
  congr 1
  omega

lemma update_correct {w Q k r P S B n : ℕ} (s : Data)
    (hQ : 0<Q) (hk : 0<k) (hB : 0<B)
    (hQW : Q<wordModulus w) (hkW : k<wordModulus w) (hrW : r<wordModulus w)
    (hP : P<wordModulus w) (hS : S<wordModulus w) (hBW : B<wordModulus w)
    (hnB : n*B<wordModulus w) (hnk : n+(k-1)<wordModulus w)
    (hnr : batchCount n k*r<wordModulus w)
    (hnext : batchCount n k*r*(B/Q)<wordModulus w)
    (h1 : s.registers 1=n*B) (h3 : s.registers 3=P)
    (h4 : s.registers 4=S) (h6 : s.registers 6=B) :
    Eval w (update Q k r) s 12 (updated s Q k r P S B n) := by
  have hn : n<wordModulus w := lt_of_le_of_lt (Nat.le_add_right _ _) hnk
  have hbq : B/Q<wordModulus w := lt_of_le_of_lt (Nat.div_le_self ..) hBW
  have hnkdiv : (n+(k-1))/k<wordModulus w :=
    lt_of_le_of_lt (Nat.div_le_self ..) hnk
  have hkr : ((n+(k-1))/k)*r<wordModulus w := by simpa only [ceil_eq hk] using hnr
  have hkrq : ((n+(k-1))/k)*r*(B/Q)<wordModulus w := by simpa only [ceil_eq hk] using hnext
  apply straight_correct
  simp [updated,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h1,h3,h4,h6,hQ.ne',hk.ne',hB.ne',Nat.mul_div_cancel _ hB,
    Nat.mod_eq_of_lt hQW,Nat.mod_eq_of_lt hkW,Nat.mod_eq_of_lt hrW,
    Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hS,Nat.mod_eq_of_lt hBW,
    Nat.mod_eq_of_lt hnB,Nat.mod_eq_of_lt hnk,Nat.mod_eq_of_lt hkrq,
    Nat.mod_eq_of_lt (show k-1<wordModulus w by omega),Function.update_idem]

def body (Q k r : ℕ) : Command := .seq (PaddedAxis.pass (k*Q) r) (update Q k r)
def loop (Q k r : ℕ) : Command := .loop .lt (.literal 0) (.register 6) (body Q k r)

def value (T Q k r : ℕ) (co : ℕ → ℕ) : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0,_,x => x
  | d+1,t,x => value T Q k r co d (batchCount t k*r)
      (mapValue T (k*Q) r (Q^d) (PaddedAxis.pad x (t*Q^(d+1))) co)

def capacity (Q k r : ℕ) : ℕ → ℕ → ℕ
  | 0,t => t
  | d+1,t => max (batchCount t k*(k*Q)*Q^d)
      (max (batchCount t k*r*Q^d) (capacity Q k r d (batchCount t k*r)))

def finalCount (k r : ℕ) : ℕ → ℕ → ℕ
  | 0,t => t
  | d+1,t => finalCount k r d (batchCount t k*r)

end DeterministicThreeSum.Structured.Indexed.MatrixDown

namespace DeterministicThreeSum.Structured.Indexed.MatrixDown
open Command DeterministicThreeSum.Rectangular Axis

lemma capacity_output (Q k r d t : ℕ) :
    batchCount t k*r*tensorStride Q d ≤ capacity Q k r d t := by
  cases d with
  | zero => simp [tensorStride,capacity]
  | succ d => exact (le_max_left _ _).trans (le_max_right _ _)

lemma capacity_input {Q k r d t : ℕ} (hk : 0<k) :
    t*Q^d ≤ capacity Q k r d t := by
  cases d with
  | zero => simp [capacity]
  | succ d =>
    have h := Nat.mul_le_mul_right (Q^(d+1)) (batchCount_covers t k hk)
    have he : k*batchCount t k*Q^(d+1)=batchCount t k*(k*Q)*Q^d := by
      rw [pow_succ]; ring
    rw [he] at h
    exact h.trans (le_max_left _ _)

lemma batch_pos {t k : ℕ} (ht : 0<t) (hk : 0<k) : 0<batchCount t k := by
  have h:=batchCount_covers t k hk
  by_contra hn
  have hz : batchCount t k=0 := by omega
  simp only [hz] at h
  omega

lemma batch_le {k : ℕ} (hk : 0<k) (t : ℕ) : batchCount t k ≤ t+k := by
  rw [← ceil_eq hk]
  exact (Nat.div_le_self ..).trans (by omega)

theorem loop_correct {w T Q k r L d t P S C : ℕ} (state : Data) (x co : ℕ → ℕ)
    (hQ : 1<Q) (hk : 0<k) (hr : 0<r) (ht : 0<t) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hL : capacity Q k r d t≤L)
    (hLw : (L+k)*r+L+k+Q+r+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+r*(k*Q)<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+r*(k*Q)≤P ∨ P+L≤C) (hCS : C+r*(k*Q)≤S ∨ S+L≤C)
    (hregs : ∀ a : Fin 8, state.registers a.val=
      environment T (batchCount t k*r*tensorStride Q d) P S C (tensorStride Q d) (t*Q^d) 0 a)
    (hx : ∀ i, i<t*Q^d → state.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*(k*Q) → state.memory (C+i)=some (co i) ∧ co i<T) :
    ∃ cost out, Eval w (loop Q k r) state cost out ∧
      cost≤(((PaddedAxis.row (k*Q) r).cost+5)*L+15)*d+1 ∧
      (∀ a : Fin 8, out.registers a.val=
        environment T 0 (banks d P S).1 (banks d P S).2 C 0 (finalCount k r d t) 0 a) ∧
      (∀ j, j<finalCount k r d t → out.memory ((banks d P S).2+j)=some (value T Q k r co d t x j) ∧
        value T Q k r co d t x j<T) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) → out.memory a=state.memory a) := by
  induction d generalizing t P S state x with
  | zero =>
    have h6 : state.registers 6=0 := by simpa [environment,tensorStride] using hregs ⟨6,by omega⟩
    have htest : test w state .lt (.literal 0) (.register 6)=false := by
      simp [test,operand_literal,operand_register,evalTest,h6]
    refine ⟨1,state,Eval.loopFalse htest,by simp,?_,?_,by simp⟩
    · simpa only [tensorStride,Nat.mul_zero,banks_zero,pow_zero,Nat.mul_one,finalCount] using hregs
    · simpa only [value,banks_zero,pow_zero,Nat.mul_one,finalCount] using hx
  | succ d ih =>
    have hlenX : batchCount t k*(k*Q)*Q^d≤L := (le_max_left _ _).trans hL
    have hlenY : batchCount t k*r*Q^d≤L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
    have hlenNext : capacity Q k r d (batchCount t k*r)≤L :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hL
    have hp : 0<Q^d := pow_pos (by omega) _
    have hn : 0<batchCount t k*r := Nat.mul_pos (batch_pos ht hk) hr
    have hB : Q^d≤L := (by simpa using Nat.mul_le_mul_right (Q^d) hn : Q^d≤batchCount t k*r*Q^d) |>.trans hlenY
    have hnL : batchCount t k*r≤L :=
      (by simpa using Nat.mul_le_mul_left (batchCount t k*r) hp : batchCount t k*r≤batchCount t k*r*Q^d) |>.trans hlenY
    have hnr : batchCount (batchCount t k*r) k*r<wordModulus w := by
      have hh := Nat.mul_le_mul_right r ((batch_le hk (batchCount t k*r)).trans (Nat.add_le_add_right hnL k))
      omega
    have hnext : batchCount (batchCount t k*r) k*r*(Q^d/Q)<wordModulus w := by
      rw [tensorStride_div hQ]
      have hh := (capacity_output Q k r d (batchCount t k*r)).trans hlenNext
      omega
    have h6 : state.registers 6=Q^d := by simpa [environment,tensorStride] using hregs ⟨6,by omega⟩
    have htest : test w state .lt (.literal 0) (.register 6)=true := by
      simp [test,operand_literal,operand_register,evalTest,h6,
        Nat.mod_eq_of_lt (show Q^d<wordModulus w by omega),hp]
    have hin : t*Q^(d+1)≤batchCount t k*(k*Q)*Q^d := by
      have hh := Nat.mul_le_mul_right (Q^(d+1)) (batchCount_covers t k hk)
      convert hh using 1
      rw [pow_succ]
      ring
    have hregs' : ∀ a : Fin 8, state.registers a.val=
        environment T (batchCount t k*r*Q^d) P S C (Q^d) (t*Q^(d+1)) 0 a := hregs
    obtain ⟨cost,u,ep,hcost,hframe,hidx,hmem,houtside⟩ := PaddedAxis.pass_correct state x co
      (Nat.mul_pos hk (by omega)) hr hp hT hadd hmul
      (by omega : batchCount t k*r*Q^d+1<wordModulus w) (by omega) (by omega) hC hin
      (by omega) (by omega) hregs' hx hc
    have hparam : ∀ a : Fin 8, a.val≠0 → u.registers a.val=
        environment T (batchCount t k*r*Q^d) P S C (Q^d) (t*Q^(d+1)) 0 a :=
      fun a ha => (hframe a.val a.isLt ha).trans (hregs' a)
    have h1u : u.registers 1=batchCount t k*r*Q^d := by simpa [environment] using hparam ⟨1,by omega⟩ (by norm_num)
    have h3u : u.registers 3=P := by simpa [environment] using hparam ⟨3,by omega⟩ (by norm_num)
    have h4u : u.registers 4=S := by simpa [environment] using hparam ⟨4,by omega⟩ (by norm_num)
    have h6u : u.registers 6=Q^d := by simpa [environment] using hparam ⟨6,by omega⟩ (by norm_num)
    have eu := update_correct u (by omega : 0<Q) hk hp (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hnr hnext h1u h3u h4u h6u
    let v := updated u Q k r P S (Q^d) (batchCount t k*r)
    have hregsv : ∀ a : Fin 8, v.registers a.val=
        environment T (batchCount (batchCount t k*r) k*r*tensorStride Q d)
          S P C (tensorStride Q d) ((batchCount t k*r)*Q^d) 0 a := by
      intro a
      have h2u : u.registers 2=T := by simpa [environment] using hparam ⟨2,by omega⟩ (by norm_num)
      have h5u : u.registers 5=C := by simpa [environment] using hparam ⟨5,by omega⟩ (by norm_num)
      fin_cases a <;> simp [v,updated,put,environment,tensorStride_div hQ,ceil_eq hk,h2u,h5u]
    have hc' : ∀ i, i<r*(k*Q) → v.memory (C+i)=some (co i) ∧ co i<T := by
      intro i hi
      have ho : C+i<P ∨ P+batchCount t k*r*Q^d≤C+i := by omega
      simp only [v,updated,put]
      rw [houtside _ ho]
      exact hc i hi
    have hx' : ∀ i, i<(batchCount t k*r)*Q^d → v.memory (P+i)=
        some (mapValue T (k*Q) r (Q^d) (PaddedAxis.pad x (t*Q^(d+1))) co i) ∧
          mapValue T (k*Q) r (Q^d) (PaddedAxis.pad x (t*Q^(d+1))) co i<T := by
      intro i hi
      exact ⟨hmem i hi,mapValue_lt hT _ _ _ _ _ _⟩
    obtain ⟨rest,out,er,hrcost,hregsFinal,hmFinal,houtFinal⟩ := ih v
      (mapValue T (k*Q) r (Q^d) (PaddedAxis.pad x (t*Q^(d+1))) co)
      hn hlenNext hS hP (by omega) hCS hCP hregsv hx' hc'
    refine ⟨1+(cost+12)+1+rest,out,Eval.loopTrue htest (Eval.seq ep eu) er,?_,?_,?_,?_⟩
    · have hcL : cost≤((PaddedAxis.row (k*Q) r).cost+5)*L+1 := hcost.trans (by gcongr)
      nlinarith only [hcL,hrcost]
    · simpa only [banks_succ,finalCount] using hregsFinal
    · simpa only [banks_succ,value,finalCount] using hmFinal
    · intro a ha hb
      rw [houtFinal a hb ha]
      exact houtside a (by omega)

end DeterministicThreeSum.Structured.Indexed.MatrixDown
namespace DeterministicThreeSum.Structured.Indexed.MatrixDown
open Command DeterministicThreeSum.Rectangular Axis MatrixLayout
noncomputable section

def leftLeaves {T a b k r : ℕ} (f : FixedFormula (ZMod T) a b k r) :
    (d t : ℕ) → LeftBatch (ZMod T) a b d t → Fin (finalCount k r d t) → ZMod T
  | 0,_,x,z => x z 0 0
  | d+1,t,x,z => leftLeaves f d (batchCount t k*r) (childLeft f x) z

theorem value_leftLeaves {T a b k r d t : ℕ}
    (ha : 0<a) (hb : 0<b) (hr : 0<r)
    (f : FixedFormula (ZMod T) a b k r) (x : LeftBatch (ZMod T) a b d t)
    (data co : ℕ → ℕ)
    (hx : ∀ z u v, (data (z.val*(a*b)^d+pairCode a b d u v):ZMod T)=x z u v)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin a × Fin b),
      (co (s.val*(k*(a*b))+(tripleIndex k a b i).val):ZMod T)=f.left s i)
    (z : Fin (finalCount k r d t)) :
    (value T (a*b) k r co d t data z.val : ZMod T)=leftLeaves f d t x z := by
  induction d generalizing t data with
  | zero => simpa only [value,leftLeaves,pairCode,pow_zero,Nat.mul_one,Nat.add_zero] using hx z 0 0
  | succ d ih =>
    apply ih (childLeft f x) (mapValue T (k*(a*b)) r ((a*b)^d)
      (PaddedAxis.pad data (t*((a*b)^(d+1)))) co)
    intro j u v
    obtain ⟨⟨g,s⟩,rfl⟩ := finProdFinEquiv.surjective j
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_mk,Nat.add_comm,Nat.mul_comm] using
      left_level_value ha hb hr f x data co hx hc g s u v

theorem left_loop_correct {w T a b k r L d t P S C : ℕ}
    (state : Data) (f : FixedFormula (ZMod T) a b k r)
    (x : LeftBatch (ZMod T) a b d t) (data co : ℕ → ℕ)
    (ha : 0<a) (hb : 0<b) (hQ : 1<a*b) (hk : 0<k) (hr : 0<r) (ht : 0<t) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hL : capacity (a*b) k r d t≤L)
    (hLw : (L+k)*r+L+k+a*b+r+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+r*(k*(a*b))<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+r*(k*(a*b))≤P ∨ P+L≤C) (hCS : C+r*(k*(a*b))≤S ∨ S+L≤C)
    (hregs : ∀ z : Fin 8, state.registers z.val=
      environment T (batchCount t k*r*tensorStride (a*b) d) P S C
        (tensorStride (a*b) d) (t*(a*b)^d) 0 z)
    (hx : ∀ i, i<t*(a*b)^d → state.memory (S+i)=some (data i) ∧ data i<T)
    (hc : ∀ i, i<r*(k*(a*b)) → state.memory (C+i)=some (co i) ∧ co i<T)
    (hsource : ∀ z u v, (data (z.val*(a*b)^d+pairCode a b d u v):ZMod T)=x z u v)
    (hformula : ∀ (s : Fin r) (i : Fin k × Fin a × Fin b),
      (co (s.val*(k*(a*b))+(tripleIndex k a b i).val):ZMod T)=f.left s i) :
    ∃ cost out, Eval w (loop (a*b) k r) state cost out ∧
      cost≤(((PaddedAxis.row (k*(a*b)) r).cost+5)*L+15)*d+1 ∧
      (∀ z : Fin 8, out.registers z.val=
        environment T 0 (banks d P S).1 (banks d P S).2 C 0 (finalCount k r d t) 0 z) ∧
      (∀ z : Fin (finalCount k r d t), ∃ n,
        out.memory ((banks d P S).2+z.val)=some n ∧ n<T ∧
          (n:ZMod T)=leftLeaves f d t x z) ∧
      (∀ addr, (addr<P ∨ P+L≤addr) → (addr<S ∨ S+L≤addr) → out.memory addr=state.memory addr) := by
  obtain ⟨cost,out,he,hcost,hregsFinal,hm,ho⟩ := loop_correct state data co hQ hk hr ht hT
    hadd hmul hL hLw hP hS hC hPS hCP hCS hregs hx hc
  refine ⟨cost,out,he,hcost,hregsFinal,?_,ho⟩
  intro z
  exact ⟨_,(hm z.val z.isLt).1,(hm z.val z.isLt).2,
    value_leftLeaves ha hb hr f x data co hsource hformula z⟩

end
end DeterministicThreeSum.Structured.Indexed.MatrixDown

namespace DeterministicThreeSum.Structured.Indexed.MatrixDown
open Command DeterministicThreeSum.Rectangular Axis MatrixLayout
noncomputable section

def rightLeaves {T a b k r : ℕ} (f : FixedFormula (ZMod T) a b k r) :
    (d t : ℕ) → RightBatch (ZMod T) a b d t → Fin (finalCount k r d t) → ZMod T
  | 0,_,y,z => y z 0 0
  | d+1,t,y,z => rightLeaves f d (batchCount t k*r) (childRight f y) z

theorem value_rightLeaves {T a b k r d t : ℕ}
    (ha : 0<a) (hb : 0<b) (hr : 0<r)
    (f : FixedFormula (ZMod T) a b k r) (y : RightBatch (ZMod T) a b d t)
    (data co : ℕ → ℕ)
    (hy : ∀ z u v, (data (z.val*(b*a)^d+pairCode b a d u v):ZMod T)=y z u v)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin b × Fin a),
      (co (s.val*(k*(b*a))+(tripleIndex k b a i).val):ZMod T)=f.right s i)
    (z : Fin (finalCount k r d t)) :
    (value T (b*a) k r co d t data z.val : ZMod T)=rightLeaves f d t y z := by
  induction d generalizing t data with
  | zero => simpa only [value,rightLeaves,pairCode,pow_zero,Nat.mul_one,Nat.add_zero] using hy z 0 0
  | succ d ih =>
    apply ih (childRight f y) (mapValue T (k*(b*a)) r ((b*a)^d)
      (PaddedAxis.pad data (t*((b*a)^(d+1)))) co)
    intro j u v
    obtain ⟨⟨g,s⟩,rfl⟩ := finProdFinEquiv.surjective j
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_mk,Nat.add_comm,Nat.mul_comm] using
      right_level_value ha hb hr f y data co hy hc g s u v

end
end DeterministicThreeSum.Structured.Indexed.MatrixDown

end OAI
