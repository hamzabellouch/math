import Mathlib
import OAI.Computability.DeterministicSum.MatrixUp

namespace OAI

/-! Charged scalar leaves and exact source bilinear product assembly. -/

namespace DeterministicThreeSum.Structured.MatrixLeaves
open Command

def body : Command := straight [
  .binary 6 .add (.register 0) (.register 3), .load 7 (.register 6),
  .binary 6 .add (.register 1) (.register 3), .load 8 (.register 6),
  .binary 7 .mul (.register 7) (.register 8),
  .binary 7 .rem (.register 7) (.register 5),
  .binary 6 .add (.register 2) (.register 3), .store (.register 6) (.register 7)]

theorem body_correct {w T A B P n i : ℕ} (s : Data) (x y : ℕ → ℕ)
    (hi : i<n) (hT : 0<T) (hmul : T*T<wordModulus w)
    (hA : A+n<wordModulus w) (hB : B+n<wordModulus w) (hP : P+n<wordModulus w)
    (h0 : s.registers 0=A) (h1 : s.registers 1=B) (h2 : s.registers 2=P)
    (h3 : s.registers 3=i) (h5 : s.registers 5=T)
    (hx : x i<T) (hy : y i<T)
    (hmx : s.memory (A+i)=some (x i)) (hmy : s.memory (B+i)=some (y i)) :
    ∃ t, Eval w body s 8 t ∧
      (∀ r, r≤5 ∨ 9≤r → t.registers r=s.registers r) ∧
      t.memory=Function.update s.memory (P+i) (some ((x i*y i)%T)) := by
  have hTT : T≤T*T := by simpa using Nat.mul_le_mul_left T hT
  have hTW : T<wordModulus w := hTT.trans_lt hmul
  have hxy : x i*y i<wordModulus w :=
    (Nat.mul_le_mul (Nat.le_of_lt hx) (Nat.le_of_lt hy)).trans_lt hmul
  have hmod : (x i*y i)%T<wordModulus w := (Nat.mod_lt _ hT).trans hTW
  let u:=put (put (put (put (put (put (put s 6 (A+i)) 7 (x i)) 6 (B+i)) 8 (y i))
    7 (x i*y i)) 7 ((x i*y i)%T)) 6 (P+i)
  let t : Data := {u with memory:=Function.update s.memory (P+i) (some ((x i*y i)%T))}
  refine ⟨t,?_,?_,rfl⟩
  · apply straight_correct
    simp [execStraight,Atom.eval,evalBinOp,operand_register,h0,h1,h2,h3,h5,put,u,t,
      Nat.mod_eq_of_lt hTW,Nat.mod_eq_of_lt hxy,Nat.mod_eq_of_lt hmod,
      Nat.mod_eq_of_lt (show A<wordModulus w by omega),
      Nat.mod_eq_of_lt (show i<wordModulus w by omega),
      Nat.mod_eq_of_lt (show A+i<wordModulus w by omega),
      Nat.mod_eq_of_lt (show B+i<wordModulus w by omega),
      Nat.mod_eq_of_lt (show P+i<wordModulus w by omega),hmx,hmy,ne_of_gt hT]
  · intro r hr
    simp only [t,u,put,Function.update_of_ne (by omega : r≠6),
      Function.update_of_ne (by omega : r≠7),Function.update_of_ne (by omega : r≠8)]

def command : Command := .seq (.atom (.assign 3 (.literal 0))) (indexedLoop 3 4 body)

theorem command_correct {w T A B P n : ℕ} (s : Data) (x y : ℕ → ℕ)
    (hT : 0<T) (hmul : T*T<wordModulus w)
    (hA : A+n<wordModulus w) (hB : B+n<wordModulus w) (hP : P+n+1<wordModulus w)
    (hAP : A+n≤P ∨ P+n≤A) (hBP : B+n≤P ∨ P+n≤B)
    (h0 : s.registers 0=A) (h1 : s.registers 1=B) (h2 : s.registers 2=P)
    (h4 : s.registers 4=n) (h5 : s.registers 5=T)
    (hx : ∀ i, i<n → s.memory (A+i)=some (x i) ∧ x i<T)
    (hy : ∀ i, i<n → s.memory (B+i)=some (y i) ∧ y i<T) :
    ∃ cost t, Eval w command s cost t ∧ cost≤11*n+2 ∧
      (∀ r, r≤2 ∨ r=4 ∨ r=5 ∨ 9≤r → t.registers r=s.registers r) ∧
      t.memory=written s P (fun i=>(x i*y i)%T) n := by
  let s0:=put s 3 0
  have e0 : Eval w (.atom (.assign 3 (.literal 0))) s 1 s0 := by
    simpa [operand_literal] using eval_assign (w:=w) s 3 (.literal 0)
  obtain ⟨cost,t,he,hc,hr,hi,ht⟩ := indexedLoop_correct (w:=w) (n:=n) (index:=3) (bound:=4) (base:=P) (K:=8)
    (by omega) (by decide) body s s0 (fun i=>(x i*y i)%T)
    (fun r=>r≤2 ∨ r=4 ∨ r=5 ∨ 9≤r) (by omega) (by omega)
    (by simpa [s0,put] using h4) (by simp [s0,put]) rfl (by
      intro i u h_i hu hindex hmem
      have hmx : u.memory (A+i)=some (x i) := by
        rw [hmem,written_outside (by omega : A+i<P ∨ P+i≤A+i)]
        exact (hx i h_i).1
      have hmy : u.memory (B+i)=some (y i) := by
        rw [hmem,written_outside (by omega : B+i<P ∨ P+i≤B+i)]
        exact (hy i h_i).1
      obtain ⟨v,ev,hv,hvm⟩ := body_correct (w:=w) (T:=T) (A:=A) (B:=B) (P:=P) (n:=n) u x y h_i hT hmul hA hB (by omega)
        (by simpa [s0,put] using (hu 0 (by omega)).trans (by simpa [s0,put] using h0))
        (by simpa [s0,put] using (hu 1 (by omega)).trans (by simpa [s0,put] using h1))
        (by simpa [s0,put] using (hu 2 (by omega)).trans (by simpa [s0,put] using h2))
        hindex
        (by simpa [s0,put] using (hu 5 (by omega)).trans (by simpa [s0,put] using h5))
        (hx i h_i).2 (hy i h_i).2 hmx hmy
      exact ⟨8,v,ev,le_rfl,fun r h=>hv r (by omega),hvm⟩)
  refine ⟨1+cost,t,Eval.seq e0 he,by omega,?_,ht⟩
  intro r h
  rw [hr r h]
  simp only [s0,put,Function.update_of_ne (by omega : r≠3)]

lemma value_modular (T a b : ℕ) : (((a*b)%T:ℕ):ZMod T)=(a:ZMod T)*(b:ZMod T) := by
  simp

end DeterministicThreeSum.Structured.MatrixLeaves
namespace DeterministicThreeSum.Structured.Indexed.MatrixUp
open Command DeterministicThreeSum.Rectangular Axis MatrixLayout MatrixDown
noncomputable section

lemma value_succ_last (T Q k r : ℕ) (co : ℕ → ℕ) (d B : ℕ) (x : ℕ → ℕ) :
    value T Q k r co (d+1) B x =
      mapValue T r (k*Q) (B*Q^d) (value T Q k r co d B x) co := by
  induction d generalizing B x with
  | zero => simp [value]
  | succ d ih =>
    change value T Q k r co (d+1) (B*Q) (mapValue T r (k*Q) B x co) =
      mapValue T r (k*Q) (B*Q^(d+1))
        (value T Q k r co d (B*Q) (mapValue T r (k*Q) B x co)) co
    rw [ih]
    congr 1
    rw [pow_succ]
    ring

theorem value_multiplyBatch {T a b k r d t : ℕ}
    (ha : 0<a) (hk : 0<k)
    (f : FixedFormula (ZMod T) a b k r)
    (x : LeftBatch (ZMod T) a b d t) (y : RightBatch (ZMod T) a b d t)
    (data co : ℕ → ℕ)
    (hdata : ∀ z : Fin (finalCount k r d t), (data z.val:ZMod T)=
      leftLeaves f d t x z * rightLeaves f d t y z)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin a × Fin a),
      (co ((tripleIndex k a a i).val*r+s.val):ZMod T)=f.out s i)
    (e : Fin t) (u v : DigitBox a d) :
    (value T (a*a) k r co d 1 data
      (e.val*((a*a)^d)+pairCode a a d u v):ZMod T)=
      multiplyBatch f hk d t x y e u v := by
  induction d generalizing t with
  | zero =>
    have hu : u=0 := Subsingleton.elim _ _
    have hv : v=0 := Subsingleton.elim _ _
    subst u; subst v
    simpa only [value,multiplyBatch,leftLeaves,rightLeaves,pairCode,pow_zero,
      Nat.mul_one,Nat.add_zero] using hdata e
  | succ d ih =>
    rw [value_succ_last]
    simp only [Nat.one_mul]
    apply combine_level_value ha hk f
      (multiplyBatch f hk d (batchCount t k*r) (childLeft f x) (childRight f y))
      (value T (a*a) k r co d 1 data) co _ hc e u v
    intro z u' v'
    exact ih (childLeft f x) (childRight f y) (by
      intro z'
      exact hdata z') z u' v'

theorem value_product {T a b k r d t : ℕ}
    (ha : 0<a) (hk : 0<k)
    (f : FixedFormula (ZMod T) a b k r)
    (hf : ∀ i j o, f.coeff i j o=(independentMatrixTensor i j o:ZMod T))
    (x : LeftBatch (ZMod T) a b d t) (y : RightBatch (ZMod T) a b d t)
    (data co : ℕ → ℕ)
    (hdata : ∀ z : Fin (finalCount k r d t), (data z.val:ZMod T)=
      leftLeaves f d t x z * rightLeaves f d t y z)
    (hc : ∀ (s : Fin r) (i : Fin k × Fin a × Fin a),
      (co ((tripleIndex k a a i).val*r+s.val):ZMod T)=f.out s i)
    (e : Fin t) (u v : DigitBox a d) :
    (value T (a*a) k r co d 1 data
      (e.val*((a*a)^d)+pairCode a a d u v):ZMod T)=(x e*y e) u v := by
  rw [value_multiplyBatch ha hk f x y data co hdata hc,
    multiplyBatch_correct f hk hf]

end
end DeterministicThreeSum.Structured.Indexed.MatrixUp

end OAI
