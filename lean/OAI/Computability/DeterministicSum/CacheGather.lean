import Mathlib
import OAI.Computability.DeterministicSum.SparseCodes

namespace OAI

/-! Charged index interleaving, coefficient gathering and row evaluation. -/

namespace DeterministicThreeSum.Structured.Indexed.ZipIndex
open Command

def value (m b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 0
  | d+1,i,j => i%m*b+j%b+(m*b)*value m b d (i/m) (j/b)
lemma value_lt {m b : ℕ} (hm : 0 < m) (hb : 0 < b) (d i j : ℕ) :
    value m b d i j < (m*b)^d := by
  induction d generalizing i j with
  | zero => simp [value]
  | succ d ih =>
    have h1:=Nat.mod_lt i hm
    have h2:=Nat.mod_lt j hb
    have h3:=ih (i/m) (j/b)
    have h4:=Nat.mul_le_mul_left (m*b) (show value m b d (i/m) (j/b)+1 ≤ (m*b)^d by omega)
    simp only [value,pow_succ']
    nlinarith only [h1,h2,h3,h4]

def step (m b : ℕ) : Command := straight [
  .binary 7 .rem (.register 1) (.literal m),
  .binary 8 .rem (.register 2) (.literal b),
  .binary 5 .add (.register 5) (.register 7),
  .binary 6 .add (.register 6) (.register 8),
  .binary 9 .mul (.register 7) (.literal b),
  .binary 9 .add (.register 9) (.register 8),
  .binary 10 .mul (.register 9) (.register 4),
  .binary 3 .add (.register 3) (.register 10),
  .binary 4 .mul (.register 4) (.literal (m*b)),
  .binary 1 .quot (.register 1) (.literal m),
  .binary 2 .quot (.register 2) (.literal b),
  .binary 0 .sub (.register 0) (.literal 1)]
def command (m b : ℕ) : Command := .loop .lt (.literal 0) (.register 0) (step m b)

def stepState (s : Data) (m b d i j a v h k : ℕ) : Data :=
  put (put (put (put (put (put (put (put (put (put (put (put s
    7 (i%m)) 8 (j%b)) 5 (h+i%m)) 6 (k+j%b)) 9 (i%m*b)) 9 (i%m*b+j%b))
    10 ((i%m*b+j%b)*v)) 3 (a+(i%m*b+j%b)*v)) 4 (v*(m*b))) 1 (i/m)) 2 (j/b)) 0 d

def Regs (s : Data) (d i j a v h k : ℕ) : Prop :=
  s.registers 0=d ∧ s.registers 1=i ∧ s.registers 2=j ∧ s.registers 3=a ∧
  s.registers 4=v ∧ s.registers 5=h ∧ s.registers 6=k

lemma step_correct {w m b d i j a v h k : ℕ} (s : Data)
    (hm : 0 < m) (hb : 0 < b) (hR : m*b < wordModulus w)
    (hd : d+1 < wordModulus w) (hi : i < wordModulus w) (hj : j < wordModulus w)
    (ha : a+(i%m*b+j%b)*v < wordModulus w) (hv : v*(m*b) < wordModulus w)
    (hh : h+i%m < wordModulus w) (hk : k+j%b < wordModulus w)
    (hr : Regs s (d+1) i j a v h k) :
    Eval w (step m b) s 12 (stepState s m b d i j a v h k) := by
  have hmW : m < wordModulus w := (by nlinarith : m ≤ m*b).trans_lt hR
  have hbW : b < wordModulus w := (by nlinarith : b ≤ m*b).trans_lt hR
  have hpair : i%m*b+j%b < m*b := by nlinarith [Nat.mod_lt i hm,Nat.mod_lt j hb]
  have hpairW:=hpair.trans hR
  have hvW : v < wordModulus w := (by simpa using Nat.mul_le_mul_left v (show 1 ≤ m*b from Nat.mul_pos hm hb) : v ≤ v*(m*b)).trans_lt hv
  have hmul : i%m*b < wordModulus w := by omega
  have htemp : (i%m*b+j%b)*v < wordModulus w := by omega
  have hidiv : i/m < wordModulus w := (Nat.div_le_self ..).trans_lt hi
  have hjdiv : j/b < wordModulus w := (Nat.div_le_self ..).trans_lt hj
  have he : d+1+wordModulus w-1=d+wordModulus w := by omega
  rcases hr with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  apply straight_correct
  simp [stepState,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h0,h1,h2,h3,h4,h5,h6,hm.ne',hb.ne',Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj,
    Nat.mod_eq_of_lt hmW,Nat.mod_eq_of_lt hbW,Nat.mod_eq_of_lt hR,Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt (show a < wordModulus w by omega),
    Nat.mod_eq_of_lt (show h < wordModulus w by omega),Nat.mod_eq_of_lt (show k < wordModulus w by omega),
    Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt hk,Nat.mod_eq_of_lt hpairW,Nat.mod_eq_of_lt hmul,
    Nat.mod_eq_of_lt htemp,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (show 1 < wordModulus w by omega),
    Nat.mod_eq_of_lt ((Nat.mod_lt i hm).trans hmW),Nat.mod_eq_of_lt ((Nat.mod_lt j hb).trans hbW),
    he,Nat.add_mod,Nat.mod_eq_of_lt (show d < wordModulus w by omega)]

theorem command_correct {w m b : ℕ} (hm : 1 < m) (hb : 1 < b) (hR : m*b < wordModulus w)
    (d i j a v h k : ℕ) (s : Data)
    (hd : d < wordModulus w) (hi : i < m^d) (hj : j < b^d)
    (hiW : i < wordModulus w) (hjW : j < wordModulus w)
    (ha : a+v*value m b d i j < wordModulus w) (hv : v*(m*b)^d < wordModulus w)
    (hh : h+DigitSum.value m d i < wordModulus w) (hk : k+DigitSum.value b d j < wordModulus w)
    (hr : Regs s d i j a v h k) :
    ∃ cost z, Eval w (command m b) s cost z ∧ cost ≤ 14*d+1 ∧ z.memory=s.memory ∧
      Regs z 0 0 0 (a+v*value m b d i j) (v*(m*b)^d)
        (h+DigitSum.value m d i) (k+DigitSum.value b d j) ∧
      (∀ r, 11 ≤ r → z.registers r=s.registers r) := by
  induction d generalizing i j a v h k s with
  | zero =>
    have hi0 : i=0 := by simpa using hi
    have hj0 : j=0 := by simpa using hj
    subst i; subst j
    refine ⟨1,s,Eval.loopFalse ?_,by omega,rfl,?_,by simp⟩
    · simp [test,operand_literal,operand_register,evalTest,hr.1]
    · simpa [value,DigitSum.value] using hr
  | succ d ih =>
    have hi' : i/m < m^d := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa only [pow_succ] using hi)
    have hj' : j/b < b^d := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa only [pow_succ] using hj)
    have hA : a+(i%m*b+j%b)*v < wordModulus w := by
      simp only [value] at ha
      have hh':=Nat.mul_le_mul_left v (Nat.le_add_right (i%m*b+j%b) ((m*b)*value m b d (i/m) (j/b)))
      have hhh:=Nat.add_le_add_left hh' a
      rw [Nat.mul_comm v (i%m*b+j%b)] at hhh
      exact hhh.trans_lt ha
    have hV : v*(m*b) < wordModulus w := by
      have hh' : 1 ≤ (m*b)^d := pow_pos (Nat.mul_pos (by omega) (by omega)) _
      rw [pow_succ'] at hv
      nlinarith
    have hH : h+i%m < wordModulus w := by simp only [DigitSum.value] at hh; omega
    have hK : k+j%b < wordModulus w := by simp only [DigitSum.value] at hk; omega
    let u:=stepState s m b d i j a v h k
    have eu:=step_correct s (by omega) (by omega) hR hd hiW hjW hA hV hH hK hr
    have hr' : Regs u d (i/m) (j/b) (a+(i%m*b+j%b)*v) (v*(m*b)) (h+i%m) (k+j%b) := by
      simp [Regs,u,stepState,put]
    obtain ⟨c,z,ez,hc,hzm,hzr,hzf⟩:=ih (i/m) (j/b) (a+(i%m*b+j%b)*v) (v*(m*b)) (h+i%m) (k+j%b) u
      (by omega) hi' hj' ((Nat.div_le_self ..).trans_lt hiW) ((Nat.div_le_self ..).trans_lt hjW)
      (by convert ha using 1; simp only [value]; ring)
      (by simpa only [pow_succ',Nat.mul_assoc] using hv)
      (by simpa only [DigitSum.value,Nat.add_assoc] using hh)
      (by simpa only [DigitSum.value,Nat.add_assoc] using hk) hr'
    refine ⟨1+12+1+c,z,Eval.loopTrue ?_ eu ez,by omega,hzm,?_,?_⟩
    · simp [test,operand_literal,operand_register,evalTest,hr.1,Nat.mod_eq_of_lt hd]
    · convert hzr using 1 <;> simp only [value,DigitSum.value,pow_succ'] <;> ring
    · intro r hr11
      rw [hzf r hr11]
      simp [u,stepState,put,show r≠0 by omega,show r≠1 by omega,show r≠2 by omega,
        show r≠3 by omega,show r≠4 by omega,show r≠5 by omega,show r≠6 by omega,
        show r≠7 by omega,show r≠8 by omega,show r≠9 by omega,show r≠10 by omega]
end DeterministicThreeSum.Structured.Indexed.ZipIndex
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command

def TailOK (tail : Bool) (H J : ℕ) : Prop := tail=false ∨ H < J
instance (tail : Bool) (H J : ℕ) : Decidable (TailOK tail H J) := inferInstanceAs (Decidable (tail=false ∨ H < J))
def loadCoefficient : Command := straight [
  .binary 10 .add (.register 16) (.register 3), .load 11 (.register 10)]
def zeroCoefficient : Command := .atom (.assign 11 (.literal 0))
def tailRead (tail : Bool) : Command :=
  if tail then .ite .lt (.register 18) (.register 6) loadCoefficient zeroCoefficient else loadCoefficient
def readCoefficient (tail : Bool) : Command := .seq
  (.atom (.binary 11 .add (.register 5) (.register 6)))
  (.ite .le (.register 11) (.register 17) (tailRead tail) zeroCoefficient)

lemma loadCoefficient_correct {w S v y : ℕ} (s : Data)
    (haddr : S+v < wordModulus w) (h16 : s.registers 16=S) (h3 : s.registers 3=v)
    (hm : s.memory (S+v)=some y) :
    ∃ z, Eval w loadCoefficient s 2 z ∧ z.registers 11=y ∧ z.memory=s.memory ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  refine ⟨put (put s 10 (S+v)) 11 y,?_,by simp [put],rfl,?_⟩
  · apply straight_correct
    simp [execStraight,Atom.eval,operand_register,evalBinOp,put,h16,h3,
      Nat.mod_eq_of_lt haddr,Nat.mod_eq_of_lt (show S < wordModulus w by omega),
      Nat.mod_eq_of_lt (show v < wordModulus w by omega),hm]
  · intro r hr; simp [put,show r≠10 by omega,show r≠11 by omega]
lemma zeroCoefficient_correct {w : ℕ} (s : Data) :
    ∃ z, Eval w zeroCoefficient s 1 z ∧ z.registers 11=0 ∧ z.memory=s.memory ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  refine ⟨put s 11 0,?_,by simp [put],rfl,?_⟩
  · simpa [zeroCoefficient,operand_literal] using eval_assign (w:=w) s 11 (.literal 0)
  · intro r hr; simp [put,show r≠11 by omega]
lemma tailRead_correct {w S v y H J : ℕ} (tail : Bool) (s : Data)
    (haddr : S+v < wordModulus w) (hH : H < wordModulus w) (hJ : J < wordModulus w)
    (h16 : s.registers 16=S) (h3 : s.registers 3=v)
    (h18 : s.registers 18=H) (h6 : s.registers 6=J)
    (hm : TailOK tail H J → s.memory (S+v)=some y) :
    ∃ cost z, Eval w (tailRead tail) s cost z ∧ cost ≤ 4 ∧
      z.registers 11=(if TailOK tail H J then y else 0) ∧ z.memory=s.memory ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  cases tail with
  | false =>
    obtain ⟨z,ez,hz,hmz,hframe⟩:=loadCoefficient_correct s haddr h16 h3 (hm (Or.inl rfl))
    exact ⟨2,z,ez,by omega,by simpa [TailOK] using hz,hmz,hframe⟩
  | true =>
    have ht : test w s .lt (.register 18) (.register 6)=decide (H < J) := by
      simp [test,operand_register,evalTest,h18,h6,Nat.mod_eq_of_lt hH,Nat.mod_eq_of_lt hJ]
    by_cases h : H < J
    · obtain ⟨z,ez,hz,hmz,hframe⟩:=loadCoefficient_correct s haddr h16 h3 (hm (Or.inr h))
      exact ⟨4,z,Eval.iteTrue (by simpa [h] using ht) ez,by omega,by simpa [TailOK,h] using hz,hmz,hframe⟩
    · obtain ⟨z,ez,hz,hmz,hframe⟩:=zeroCoefficient_correct (w:=w) s
      exact ⟨2,z,Eval.iteFalse (by simpa [h] using ht) ez,by omega,by simpa [TailOK,h] using hz,hmz,hframe⟩

theorem readCoefficient_correct {w S v y H D I J : ℕ} (tail : Bool) (s : Data)
    (haddr : S+v < wordModulus w) (hH : H < wordModulus w) (hD : D < wordModulus w)
    (hIJ : I+J < wordModulus w)
    (h16 : s.registers 16=S) (h3 : s.registers 3=v)
    (h18 : s.registers 18=H) (h17 : s.registers 17=D)
    (h5 : s.registers 5=I) (h6 : s.registers 6=J)
    (hm : I+J ≤ D → TailOK tail H J → s.memory (S+v)=some y) :
    ∃ cost z, Eval w (readCoefficient tail) s cost z ∧ cost ≤ 7 ∧
      z.registers 11=(if I+J ≤ D ∧ TailOK tail H J then y else 0) ∧ z.memory=s.memory ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  let u:=put s 11 (I+J)
  have eu : Eval w (.atom (.binary 11 .add (.register 5) (.register 6))) s 1 u := by
    apply Eval.atom
    simp [u,Atom.eval,operand_register,evalBinOp,put,h5,h6,Nat.mod_eq_of_lt hIJ,
      Nat.mod_eq_of_lt (show I < wordModulus w by omega),Nat.mod_eq_of_lt (show J < wordModulus w by omega)]
  have ht : test w u .le (.register 11) (.register 17)=decide (I+J ≤ D) := by
    simp [u,put,test,operand_register,evalTest,h17,Nat.mod_eq_of_lt hIJ,Nat.mod_eq_of_lt hD]
  by_cases h : I+J ≤ D
  · obtain ⟨c,z,ez,hc,hz,hmz,hf⟩:=tailRead_correct tail u haddr hH (by omega)
      (by simpa [u,put] using h16) (by simpa [u,put] using h3)
      (by simpa [u,put] using h18) (by simpa [u,put] using h6) (hm h)
    refine ⟨1+(1+c+1),z,Eval.seq eu (Eval.iteTrue (by simpa [h] using ht) ez),by omega,by simpa [h] using hz,hmz,?_⟩
    intro r hr; rw [hf r hr]; simp [u,put,show r≠11 by omega]
  · obtain ⟨z,ez,hz,hmz,hf⟩:=zeroCoefficient_correct (w:=w) u
    refine ⟨1+(1+1),z,Eval.seq eu (Eval.iteFalse (by simpa [h] using ht) ez),by omega,by simpa [h] using hz,hmz,?_⟩
    intro r hr; rw [hf r hr]; simp [u,put,show r≠11 by omega]
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command

def leftIndex (tail : Bool) (key i : ℕ) : ℕ := if tail then key else i
def rightIndex (tail : Bool) (key i : ℕ) : ℕ := if tail then i else key

def zipInputs (tail : Bool) (r : ℕ) : Operand :=
  match r with
  | 0 => .register 20
  | 1 => .register (if tail then 14 else 12)
  | 2 => .register (if tail then 12 else 14)
  | 4 => .literal 1
  | _ => .literal 0
def zipValues (d i j r : ℕ) : ℕ := match r with | 0 => d | 1 => i | 2 => j | 4 => 1 | _ => 0
def setupZip (tail : Bool) : Command := copyPrefix (zipInputs tail) 7

lemma setupZip_exact {w d i key : ℕ} (tail : Bool) (s : Data)
    (hW : 1 < wordModulus w) (hd : d < wordModulus w) (hi : i < wordModulus w) (hkey : key < wordModulus w)
    (h20 : s.registers 20=d) (h12 : s.registers 12=i) (h14 : s.registers 14=key) :
    Eval w (setupZip tail) s 7
      (patched s 7 (zipValues d (leftIndex tail key i) (rightIndex tail key i))) := by
  apply copyPrefix_correct
  · intro r hr v hv
    interval_cases r <;> cases tail <;> simp [zipInputs] at hv <;> subst v <;> omega
  · intro r hr
    interval_cases r <;> cases tail <;> simp [zipInputs,zipValues,leftIndex,rightIndex,
      operand_register,operand_literal,h20,h12,h14,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hkey,
      Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hW]

def outputWrite : Command := straight [
  .binary 10 .add (.register 15) (.register 12), .store (.register 10) (.register 11)]
lemma outputWrite_correct {w P i v : ℕ} (s : Data)
    (ha : P+i < wordModulus w) (hv : v < wordModulus w)
    (h15 : s.registers 15=P) (h12 : s.registers 12=i) (h11 : s.registers 11=v) :
    ∃ z, Eval w outputWrite s 2 z ∧ z.memory=Function.update s.memory (P+i) (some v) ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  let z : Data := {put s 10 (P+i) with memory:=Function.update s.memory (P+i) (some v)}
  refine ⟨z,?_,rfl,?_⟩
  · apply straight_correct
    simp [execStraight,Atom.eval,operand_register,evalBinOp,z,put,h15,h12,h11,
      Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt (show P < wordModulus w by omega),
      Nat.mod_eq_of_lt (show i < wordModulus w by omega)]
  · intro r hr; simp [z,put,show r≠10 by omega]

def gathered (tail : Bool) (m b d D H key : ℕ) (x : ℕ → ℕ) (i : ℕ) : ℕ :=
  let u:=leftIndex tail key i
  let v:=rightIndex tail key i
  if DigitSum.value m d u+DigitSum.value b d v ≤ D ∧ TailOK tail H (DigitSum.value b d v)
  then x (ZipIndex.value m b d u v) else 0

def gatherBody (tail : Bool) (m b : ℕ) : Command :=
  .seq (setupZip tail) (.seq (ZipIndex.command m b) (.seq (readCoefficient tail) outputWrite))

theorem gatherBody_correct {w m b d D H key P S i : ℕ} (tail : Bool) (s : Data) (x : ℕ → ℕ)
    (hm : 1 < m) (hb : 1 < b) (hR : m*b < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hP : P+i < wordModulus w) (hS : S+(m*b)^d < wordModulus w)
    (hl : leftIndex tail key i < m^d) (hr : rightIndex tail key i < b^d)
    (h12 : s.registers 12=i) (h14 : s.registers 14=key)
    (h15 : s.registers 15=P) (h16 : s.registers 16=S)
    (h17 : s.registers 17=D) (h18 : s.registers 18=H) (h20 : s.registers 20=d)
    (hxw : x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)) < wordModulus w)
    (hx : DigitSum.value m d (leftIndex tail key i)+DigitSum.value b d (rightIndex tail key i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail key i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))=
        some (x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)))) :
    ∃ cost z, Eval w (gatherBody tail m b) s cost z ∧ cost ≤ 14*d+17 ∧
      z.memory=Function.update s.memory (P+i) (some (gathered tail m b d D H key x i)) ∧
      ∀ r, 12 ≤ r → z.registers r=s.registers r := by
  let l:=leftIndex tail key i
  let r:=rightIndex tail key i
  have hlW : l < wordModulus w := by dsimp [l]; omega
  have hrW : r < wordModulus w := by dsimp [r]; omega
  have hi : i < wordModulus w := by cases tail <;> simp [l,r,leftIndex,rightIndex] at hlW hrW <;> omega
  have hkey : key < wordModulus w := by cases tail <;> simp [l,r,leftIndex,rightIndex] at hlW hrW <;> omega
  let u:=patched s 7 (zipValues d l r)
  have eu:=setupZip_exact tail s (by nlinarith : 1 < wordModulus w) hd hi hkey h20 h12 h14
  have hidx:=ZipIndex.value_lt (by omega : 0 < m) (by omega : 0 < b) d l r
  have hsum0 : DigitSum.value m d l+DigitSum.value b d r < wordModulus w := by
    have h1:=DigitSum.value_le hm d l
    have h2:=DigitSum.value_le hb d r
    dsimp [l,r] at *
    omega
  obtain ⟨c,v,ev,hc,hvm,hvr,hvf⟩:=ZipIndex.command_correct hm hb hR d l r 0 1 0 0 u hd hl hr hlW hrW
    (by simpa using hidx.trans hvol) (by simpa using hvol)
    (by simpa using (show DigitSum.value m d l < wordModulus w by omega))
    (by simpa using (show DigitSum.value b d r < wordModulus w by omega))
    (by simp [u,patched,zipValues,ZipIndex.Regs])
  have hvctx : ∀ a, 12 ≤ a → v.registers a=s.registers a := by
    intro a ha; rw [hvf a (by omega)]; simp [u,patched,show ¬a < 7 by omega]
  obtain ⟨c',v',ev',hc',hv11,hv'm,hv'f⟩:=readCoefficient_correct tail v
    (by omega : S+ZipIndex.value m b d l r < wordModulus w) hH hD hsum0
    ((hvctx 16 (by omega)).trans h16) (by simpa [ZipIndex.Regs] using hvr.2.2.2.1)
    ((hvctx 18 (by omega)).trans h18) ((hvctx 17 (by omega)).trans h17)
    (by simpa using hvr.2.2.2.2.2.1) (by simpa using hvr.2.2.2.2.2.2)
    (by intro hi' ht'; rw [hvm]; exact hx hi' ht')
  have hv'ctx : ∀ a, 12 ≤ a → v'.registers a=s.registers a := fun a ha => (hv'f a ha).trans (hvctx a ha)
  have hvalue : v'.registers 11=gathered tail m b d D H key x i := hv11
  have hval : gathered tail m b d D H key x i < wordModulus w := by
    dsimp [gathered]; split_ifs <;> first | exact hxw | exact wordModulus_pos w
  obtain ⟨z,ez,hzm,hzf⟩:=outputWrite_correct v' hP hval
    ((hv'ctx 15 (by omega)).trans h15) ((hv'ctx 12 (by omega)).trans h12) hvalue
  refine ⟨7+(c+(c'+2)),z,Eval.seq eu (Eval.seq ev (Eval.seq ev' ez)),by omega,?_,?_⟩
  · rw [hzm,hv'm,hvm]; rfl
  · intro a ha; exact (hzf a ha).trans (hv'ctx a ha)
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command

def gatherRow (tail : Bool) (m b : ℕ) : Command :=
  .seq (.atom (.assign 12 (.literal 0))) (indexedLoop 12 13 (gatherBody tail m b))

theorem gatherRow_correct {w m b d D H key P S N : ℕ} (tail : Bool) (s : Data) (x : ℕ → ℕ)
    (hm : 1 < m) (hb : 1 < b) (hR : m*b < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hN : N+1 < wordModulus w) (hP : P+N < wordModulus w)
    (hS : S+(m*b)^d < wordModulus w) (hdisj : P+N ≤ S ∨ S+(m*b)^d ≤ P)
    (hl : ∀ i, i < N → leftIndex tail key i < m^d)
    (hr : ∀ i, i < N → rightIndex tail key i < b^d)
    (h13 : s.registers 13=N) (h14 : s.registers 14=key)
    (h15 : s.registers 15=P) (h16 : s.registers 16=S)
    (h17 : s.registers 17=D) (h18 : s.registers 18=H) (h20 : s.registers 20=d)
    (hxw : ∀ i, i < N → x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)) < wordModulus w)
    (hx : ∀ i, i < N →
      DigitSum.value m d (leftIndex tail key i)+DigitSum.value b d (rightIndex tail key i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail key i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i))=
        some (x (ZipIndex.value m b d (leftIndex tail key i) (rightIndex tail key i)))) :
    ∃ cost z, Eval w (gatherRow tail m b) s cost z ∧ cost ≤ (14*d+20)*N+2 ∧
      z.memory=written s P (gathered tail m b d D H key x) N ∧ z.registers 12=N ∧
      ∀ r, 13 ≤ r → z.registers r=s.registers r := by
  let u:=put s 12 0
  have eu : Eval w (.atom (.assign 12 (.literal 0))) s 1 u := by
    apply Eval.atom
    simp [Atom.eval,operand_literal,u]
  have hu : ∀ r, 13 ≤ r → u.registers r=s.registers r := by
    intro r hr'; simp [u,put,show r≠12 by omega]
  obtain ⟨c,z,ez,hc,hzr,hz12,hzm⟩:=indexedLoop_correct hN (by omega : 12≠13)
    (gatherBody tail m b) s u (gathered tail m b d D H key x) (fun r=>13 ≤ r)
    (by omega) (by omega) ((hu 13 (by omega)).trans h13) (by simp [u,put]) rfl
    (base:=P) (K:=14*d+17) (by
      intro i t hi ht ht12 htm
      have hctx : ∀ r, 13 ≤ r → t.registers r=s.registers r := fun r hr' => (ht r hr').trans (hu r hr')
      obtain ⟨c',v,ev,hc',hvm,hvr⟩:=gatherBody_correct tail t x hm hb hR hd hD hH hvol hsum
        (by omega : P+i < wordModulus w) hS (hl i hi) (hr i hi) ht12
        ((hctx 14 (by omega)).trans h14) ((hctx 15 (by omega)).trans h15)
        ((hctx 16 (by omega)).trans h16) ((hctx 17 (by omega)).trans h17)
        ((hctx 18 (by omega)).trans h18) ((hctx 20 (by omega)).trans h20) (hxw i hi)
        (by
          intro hg htail
          rw [htm,written_outside]
          · exact hx i hi hg htail
          · have hv:=ZipIndex.value_lt (by omega : 0 < m) (by omega : 0 < b) d
              (leftIndex tail key i) (rightIndex tail key i)
            omega)
      exact ⟨c',v,ev,hc',fun r hr' => hvr r (by rcases hr' with hr'|hr' <;> omega),hvm⟩)
  refine ⟨1+c,z,Eval.seq eu ez,by nlinarith only [hc],hzm,hz12,?_⟩
  intro r hr'; exact (hzr r hr').trans (hu r hr')
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Axis SparseAxis DeterministicThreeSum.Rectangular Finset
open scoped BigOperators

def zipDigit (m b : ℕ) : (d : ℕ) → DigitBox m d → DigitBox b d → DigitBox (m*b) d
  | 0,_,_ => 0
  | d+1,u,v => (⟨u.1.val*b+v.1.val, by
      have hu:=u.1.isLt
      have hv:=v.1.isLt
      have hh:=Nat.mul_le_mul_right b (show u.1.val+1 ≤ m by omega)
      nlinarith only [hh,hv]⟩,zipDigit m b d u.2 v.2)

lemma lowCode_parts {q : ℕ} (d : ℕ) (u : DigitBox q (d+1)) :
    lowCode q (d+1) u%q=u.1.val ∧ lowCode q (d+1) u/q=lowCode q d u.2 := by
  have hq : 0 < q := Nat.zero_lt_of_lt u.1.isLt
  constructor
  · simp [lowCode,Nat.add_mod,Nat.mod_eq_of_lt u.1.isLt]
  · rw [lowCode,Nat.add_comm,Nat.mul_add_div hq,Nat.div_eq_of_lt u.1.isLt,Nat.add_zero]

lemma zipValue_lowCode (m b d : ℕ) (u : DigitBox m d) (v : DigitBox b d) :
    ZipIndex.value m b d (lowCode m d u) (lowCode b d v)=lowCode (m*b) d (zipDigit m b d u v) := by
  induction d with
  | zero => simp [ZipIndex.value,lowCode]
  | succ d ih =>
    rw [ZipIndex.value,(lowCode_parts d u).1,(lowCode_parts d v).1,
      (lowCode_parts d u).2,(lowCode_parts d v).2,ih]
    rfl

lemma digitSum_lowCode (q d : ℕ) (u : DigitBox q d) :
    DigitSum.value q d (lowCode q d u)=∑ k, (digitFunction q d u k).val := by
  induction d with
  | zero => simp [DigitSum.value]
  | succ d ih =>
    rw [DigitSum.value,(lowCode_parts d u).1,(lowCode_parts d u).2,ih]
    simp [Fin.sum_univ_succ,digitFunction]

lemma digitFunction_zip (m b d : ℕ) (u : DigitBox m d) (v : DigitBox b d) (k : Fin d) :
    (digitFunction (m*b) d (zipDigit m b d u v) k).val=
      (digitFunction m d u k).val*b+(digitFunction b d v k).val := by
  induction d with
  | zero => exact Fin.elim0 k
  | succ d ih =>
    refine Fin.cases ?_ (fun k=>?_) k
    · rfl
    · exact ih u.2 v.2 k

lemma gathered_U (m b d D H : ℕ) (x : ℕ → ℕ)
    (u : DigitBox m d) (v : DigitBox b d) :
    gathered false m b d D H (lowCode b d v) x (lowCode m d u)=
      if (∑ k, (digitFunction m d u k).val)+(∑ k, (digitFunction b d v k).val) ≤ D
      then x (lowCode (m*b) d (zipDigit m b d u v)) else 0 := by
  simp [gathered,leftIndex,rightIndex,TailOK,digitSum_lowCode,zipValue_lowCode]

lemma gathered_W (m b d D H : ℕ) (x : ℕ → ℕ)
    (u : DigitBox m d) (v : DigitBox b d) :
    gathered true m b d D H (lowCode m d u) x (lowCode b d v)=
      if (∑ k, (digitFunction m d u k).val)+(∑ k, (digitFunction b d v k).val) ≤ D ∧
        H < ∑ k, (digitFunction b d v k).val
      then x (lowCode (m*b) d (zipDigit m b d u v)) else 0 := by
  simp [gathered,leftIndex,rightIndex,TailOK,digitSum_lowCode,zipValue_lowCode]
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command Axis

def evaluationSources (i : ℕ) : Operand := match i with
  | 1 => .register 22 | 2 => .register 23 | 3 => .register 25
  | 4 => .register 15 | 5 => .register 24 | 6 => .register 21
  | 7 => .literal 1 | _ => .literal 0

def evaluationSetup : Command := copyPrefix evaluationSources 8

lemma evaluationSetup_correct {w T N V P C B : ℕ} (s : Data)
    (hN : N < wordModulus w) (hT : T < wordModulus w) (hV : V < wordModulus w)
    (hP : P < wordModulus w) (hC : C < wordModulus w) (hB : B < wordModulus w)
    (hW : 1 < wordModulus w)
    (h22 : s.registers 22=N) (h23 : s.registers 23=T) (h25 : s.registers 25=V)
    (h15 : s.registers 15=P) (h24 : s.registers 24=C) (h21 : s.registers 21=B) :
    Eval w evaluationSetup s 8
      (patched s 8 (NewtonPass.tensorValues T N V P C B 1)) := by
  apply copyPrefix_correct
  · intro i hi r hr
    interval_cases i <;> simp [evaluationSources] at hr <;> subst r <;> omega
  · intro i hi
    interval_cases i <;> simp [evaluationSources,NewtonPass.tensorValues,operand_register,
      operand_literal,h22,h23,h25,h15,h24,h21,Nat.mod_eq_of_lt hN,Nat.mod_eq_of_lt hT,
      Nat.mod_eq_of_lt hV,Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt hB,Nat.mod_eq_of_lt hW]

def evaluateRow (tail : Bool) (m b q : ℕ) : Command :=
  .seq (gatherRow tail m b) (.seq evaluationSetup (tensorCommand q q))

theorem evaluateRow_correct {w T m b q d D H key P S V C L : ℕ}
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
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T) :
    ∃ cost z, Eval w (evaluateRow tail m b q) s cost z ∧
      cost ≤ (14*d+20)*q^d+(((row q q).cost+5)*L+11)*d+11 ∧
      (∀ i, i < q^d → z.memory ((banks d V P).2+i)=some
        (tensorValue T q q c d (gathered tail m b d D H key x) i) ∧
        tensorValue T q q c d (gathered tail m b d D H key x) i < T) ∧
      (∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) → z.memory a=s.memory a) := by
  have hTw : T < wordModulus w := by omega
  have hQi : q^d+1 < wordModulus w := by omega
  obtain ⟨a,u,eu,ha,hum,hu12,hur⟩:=gatherRow_correct tail s x hm hb hR hd hD hH hvol hsum
    hQi (by omega) hS (by omega) hl hr h13 h14 h15 h16 h17 h18 h20
    (fun i hi => (hxw i hi).trans hTw) hx
  have hN : q*tensorStride q d < wordModulus w := by
    have hh:=NewtonPass.initialCount_le (A:=1) hq d
    simp only [one_mul] at hh
    omega
  have hB : tensorStride q d < wordModulus w := (NewtonPass.tensorStride_le hq d).trans_lt (by omega)
  let v:=patched u 8 (NewtonPass.tensorValues T (q*tensorStride q d) V P C (tensorStride q d) 1)
  have ev:=evaluationSetup_correct u hN hTw (by omega) (by omega) (by omega) hB (by omega)
    ((hur 22 (by omega)).trans h22) ((hur 23 (by omega)).trans h23)
    ((hur 25 (by omega)).trans h25) ((hur 15 (by omega)).trans h15)
    ((hur 24 (by omega)).trans h24) ((hur 21 (by omega)).trans h21)
  have hvregs : ∀ i : Fin 8, v.registers i.val=
      environment T (1*q*tensorStride q d) V P C (tensorStride q d) 1 0 i := by
    intro i
    simp only [v,patched,ite_eq_left i.isLt,one_mul,NewtonPass.tensorValues_environment]
  have hvg : ∀ i, i < 1*q^d → v.memory (P+i)=some (gathered tail m b d D H key x i) ∧
      gathered tail m b d D H key x i < T := by
    intro i hi
    have hi' : i < q^d := by simpa using hi
    constructor
    · change u.memory (P+i)=_
      rw [hum]
      simp [written,hi']
    · dsimp [gathered]; split_ifs <;> first | exact hxw i hi' | exact hT
  have hvc : ∀ i, i < q*q → v.memory (C+i)=some (c i) ∧ c i < T := by
    intro i hi
    change u.memory (C+i)=_ ∧ _
    rw [hum,written_outside (by omega : C+i < P ∨ P+q^d ≤ C+i)]
    exact hc i hi
  obtain ⟨b,z,ez,hb',hzr,hzm,hzf⟩:=tensorCommand_correct v (gathered tail m b d D H key x) c
    hq (by omega) (by omega : 0 < 1) hT hadd hmul
    (by simpa only [max_self,one_mul] using hL) hLw hV hP hC hVP hCV hCP hvregs hvg hvc
  refine ⟨a+(8+b),z,Eval.seq eu (Eval.seq ev ez),by omega,?_,?_⟩
  · simpa only [one_mul] using hzm
  · intro j hjP hjV
    rw [hzf j hjV hjP]
    change u.memory j=s.memory j
    rw [hum]
    exact written_outside (by omega)
end DeterministicThreeSum.Structured.Indexed.Cache

end OAI
