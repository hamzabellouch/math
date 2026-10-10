import Mathlib
import OAI.Computability.DeterministicSum.AxisMaps
import OAI.Computability.DeterministicSum.DegreeFilter

namespace OAI

/-! Structured Newton transform commands and memory frames. -/

namespace DeterministicThreeSum.Structured
open Command

def copyPrefix (f : ℕ → Operand) : ℕ → Command
  | 0 => .skip
  | n+1 => .seq (copyPrefix f n) (.atom (.assign n (f n)))

def patched (s : Data) (n : ℕ) (v : ℕ → ℕ) : Data :=
  {s with registers:=fun r => if r<n then v r else s.registers r}

lemma patched_zero (s : Data) (v : ℕ → ℕ) : patched s 0 v=s := by
  cases s; simp [patched]

lemma patched_succ (s : Data) (n : ℕ) (v : ℕ → ℕ) :
    put (patched s n v) n (v n)=patched s (n+1) v := by
  apply Data.ext
  · funext r
    by_cases h : r=n
    · subst r; simp [patched,put]
    · simp [patched,put,h,show (r≤n)↔r<n by omega]
  · rfl

lemma copyPrefix_correct {w N : ℕ} (f : ℕ → Operand) (s : Data) (v : ℕ → ℕ)
    (hsource : ∀ i, i<N → ∀ r, f i=.register r → N≤r)
    (hval : ∀ i, i<N → operand w s (f i)=v i) :
    Eval w (copyPrefix f N) s N (patched s N v) := by
  induction N with
  | zero => simpa [copyPrefix,patched_zero] using Eval.skip (w:=w) s
  | succ N ih =>
    have hsrc : ∀ i, i<N → ∀ r, f i=.register r → N≤r := by
      intro i hi r hr; exact Nat.le_of_succ_le (hsource i (by omega) r hr)
    have eh:=ih hsrc (fun i hi => hval i (by omega))
    have hv : operand w (patched s N v) (f N)=v N := by
      rw [← hval N (by omega)]
      cases hf : f N with
      | literal a => rfl
      | register r =>
        have hh:=hsource N (by omega) r hf
        simp [operand_register,patched,show ¬r<N by omega]
    have ea : Eval w (.atom (.assign N (f N))) (patched s N v) 1 (put (patched s N v) N (v N)) := by
      apply Eval.atom; simp [Atom.eval,hv]
    rw [patched_succ] at ea
    exact Eval.seq eh ea

lemma copyPrefix_writes (f : ℕ → Operand) (N : ℕ) :
    (copyPrefix f N).writes⊆Finset.range N := by
  induction N with
  | zero => simp [copyPrefix,Command.writes]
  | succ N ih =>
    intro r hr
    simp only [copyPrefix,Command.writes,Atom.writes,Finset.mem_union,Finset.mem_singleton] at hr
    rcases hr with hr|rfl
    · exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (ih hr)) (by omega))
    · simp

lemma protected_frame {w cost k : ℕ} {s t : Data} {c : Command}
    (he : Eval w c s cost t) (hk : c.writes.sup id < k) (i : ℕ) :
    t.registers (k+i)=s.registers (k+i) := by
  apply register_frame he
  intro hf
  have hle : k+i≤c.writes.sup id := Finset.le_sup (f:=id) hf
  omega
end DeterministicThreeSum.Structured
namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis

def context (A B N Q D C T i : ℕ) : ℕ := match i with
  | 0 => A | 1 => B | 2 => N | 3 => Q | 4 => D | 5 => C | 6 => T | 7 => A*Q | _ => 0

def saveBanks (k : ℕ) : Command := straight [
  .assign (k+8) (.register 3), .assign (k+9) (.register 4)]

def savedBanks (s : Data) (k P S : ℕ) : Data := put (put s (k+8) P) (k+9) S

lemma saveBanks_correct {w k P S : ℕ} (s : Data) (_hk : 16≤k)
    (hP : P<wordModulus w) (hS : S<wordModulus w)
    (h3 : s.registers 3=P) (h4 : s.registers 4=S) :
    Eval w (saveBanks k) s 2 (savedBanks s k P S) := by
  apply straight_correct
  simp [savedBanks,execStraight,Atom.eval,operand_register,put,h3,h4,
    Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hS]

def degreeSources (k i : ℕ) : Operand := match i with
  | 1 => .register (k+7) | 2 => .register (k+9)
  | 3 => .register (k+3) | 4 => .register (k+4) | _ => .literal 0

def degreeValues (N S Q D i : ℕ) : ℕ := match i with
  | 1 => N | 2 => S | 3 => Q | 4 => D | _ => 0

lemma degreeSetup_correct {w k N S Q D : ℕ} (s : Data) (hk : 16≤k)
    (hN : N<wordModulus w) (hS : S<wordModulus w) (hQ : Q<wordModulus w) (hD : D<wordModulus w)
    (h7 : s.registers (k+7)=N) (h9 : s.registers (k+9)=S)
    (h3 : s.registers (k+3)=Q) (h4 : s.registers (k+4)=D) :
    Eval w (copyPrefix (degreeSources k) 5) s 5 (patched s 5 (degreeValues N S Q D)) := by
  apply copyPrefix_correct
  · intro i hi r hr
    interval_cases i <;> simp only [degreeSources] at hr <;> cases hr <;> omega
  · intro i hi
    interval_cases i <;> simp [degreeSources,degreeValues,operand_register,operand_literal,
      h7,h9,h3,h4,Nat.mod_eq_of_lt hN,Nat.mod_eq_of_lt hS,Nat.mod_eq_of_lt hQ,Nat.mod_eq_of_lt hD]

def tensorSources (k i : ℕ) : Operand := match i with
  | 1 => .register (k+2) | 2 => .register (k+6) | 3 => .register (k+8)
  | 4 => .register (k+9) | 5 => .register (k+5) | 6 => .register (k+1)
  | 7 => .register k | _ => .literal 0

def tensorValues (T N P S C B A i : ℕ) : ℕ := match i with
  | 1 => N | 2 => T | 3 => P | 4 => S | 5 => C | 6 => B | 7 => A | _ => 0

lemma tensorValues_environment (T N P S C B A : ℕ) (i : Fin 8) :
    tensorValues T N P S C B A i.val=environment T N P S C B A 0 i := by
  fin_cases i <;> rfl

lemma tensorSetup_correct {w k T N P S C B A : ℕ} (s : Data) (hk : 16≤k)
    (hT : T<wordModulus w) (hN : N<wordModulus w) (hP : P<wordModulus w)
    (hS : S<wordModulus w) (hC : C<wordModulus w) (hB : B<wordModulus w) (hA : A<wordModulus w)
    (h0 : s.registers k=A) (h1 : s.registers (k+1)=B) (h2 : s.registers (k+2)=N)
    (h5 : s.registers (k+5)=C) (h6 : s.registers (k+6)=T)
    (h8 : s.registers (k+8)=P) (h9 : s.registers (k+9)=S) :
    Eval w (copyPrefix (tensorSources k) 8) s 8
      (patched s 8 (tensorValues T N P S C B A)) := by
  apply copyPrefix_correct
  · intro i hi r hr
    interval_cases i <;> simp only [tensorSources] at hr <;> cases hr <;> omega
  · intro i hi
    interval_cases i <;> simp [tensorSources,tensorValues,operand_register,operand_literal,
      h0,h1,h2,h5,h6,h8,h9,Nat.mod_eq_of_lt hT,Nat.mod_eq_of_lt hN,Nat.mod_eq_of_lt hP,
      Nat.mod_eq_of_lt hS,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt hB,Nat.mod_eq_of_lt hA]

def command (q k : ℕ) : Command := .seq (tensorCommand q q)
  (.seq (saveBanks k) (.seq (copyPrefix (degreeSources k) 5)
    (.seq (DegreeFilter.command q) (.seq (copyPrefix (tensorSources k) 8) (tensorCommand q q)))))

def filtered (q d D : ℕ) (x : ℕ → ℕ) (i : ℕ) : ℕ :=
  if D<DigitSum.value q d (i%(q^d)) then 0 else x i

lemma banks_twice (d P S : ℕ) : banks d (banks d P S).1 (banks d P S).2=(P,S) := by
  by_cases h : Even d <;> simp [banks,h]

lemma tensorStride_le {q : ℕ} (hq : 1<q) (d : ℕ) : tensorStride q d≤q^d := by
  cases d with
  | zero => simp [tensorStride]
  | succ d => simpa [tensorStride,pow_succ] using Nat.le_mul_of_pos_right (q^d) (by omega : 0<q)

lemma initialCount_le {q A : ℕ} (_hq : 1<q) (d : ℕ) : A*q*tensorStride q d≤A*q^d := by
  cases d with
  | zero => simp [tensorStride]
  | succ d => simp [tensorStride,pow_succ',Nat.mul_assoc]
end DeterministicThreeSum.Structured.Indexed.NewtonPass
namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis

theorem command_correct {w T q L d A P S C E D k : ℕ} (s : Data) (x c e : ℕ → ℕ)
    (hk : 16≤k) (hkw : (tensorCommand q q).writes.sup id<k)
    (hq : 1<q) (hA : 0<A) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hL : A*q^d≤L) (hLw : L*q+L+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+q*q<wordModulus w) (hE : E+q*q<wordModulus w) (hD : D<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+q*q≤P ∨ P+L≤C) (hCS : C+q*q≤S ∨ S+L≤C)
    (hEP : E+q*q≤P ∨ P+L≤E) (hES : E+q*q≤S ∨ S+L≤E)
    (hregs : ∀ a : Fin 8, s.registers a.val=
      environment T (A*q*tensorStride q d) P S C (tensorStride q d) A 0 a)
    (hctx : ∀ i, i<8 → s.registers (k+i)=context A (tensorStride q d) (A*q*tensorStride q d) (q^d) D E T i)
    (hx : ∀ i, i<A*q^d → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<q*q → s.memory (C+i)=some (c i) ∧ c i<T)
    (he : ∀ i, i<q*q → s.memory (E+i)=some (e i) ∧ e i<T) :
    ∃ cost z, Eval w (command q k) s cost z ∧
      cost≤2*(((row q q).cost+5)*L+11)*d+(5*d+10)*(A*q^d)+19 ∧
      (∀ a : Fin 8, z.registers a.val=environment T 0 P S E 0 (A*q^d) 0 a) ∧
      (∀ i, i<A*q^d → z.memory (S+i)=some
        (tensorValue T q q e d (filtered q d D (tensorValue T q q c d x)) i) ∧
        tensorValue T q q e d (filtered q d D (tensorValue T q q c d x)) i<T) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) → z.memory a=s.memory a) := by
  have hq0 : 0<q := by omega
  have hQpos : 0<q^d := pow_pos hq0 _
  have hQN : q^d≤A*q^d := by simpa using Nat.mul_le_mul_right (q^d) hA
  have hAw : A<wordModulus w := by
    have hh : A≤A*q^d := by simpa using Nat.mul_le_mul_left A hQpos
    omega
  have hBw : tensorStride q d<wordModulus w := (tensorStride_le hq d).trans_lt (by omega)
  have hNw : A*q*tensorStride q d<wordModulus w := (initialCount_le hq d).trans_lt (by omega)
  have hqw : q<wordModulus w := by nlinarith
  obtain ⟨c1,t,et,hc1,htr,htm,htf⟩:=tensorCommand_correct s x c hq hq0 hA hT hadd hmul
    (by simpa only [max_self] using hL) hLw hP hS hC hPS hCP hCS hregs hx hc
  let P' := (banks d P S).1
  let S' := (banks d P S).2
  have hP' : P'+L+1<wordModulus w := by
    dsimp [P']; by_cases h : Even d <;> simp [banks,h] <;> assumption
  have hS' : S'+L+1<wordModulus w := by
    dsimp [S']; by_cases h : Even d <;> simp [banks,h] <;> assumption
  have hPS' : S'+L≤P' ∨ P'+L≤S' := by
    dsimp [P',S']; by_cases h : Even d <;> simp [banks,h]
    · exact hPS
    · exact hPS.symm
  have hEP' : E+q*q≤P' ∨ P'+L≤E := by
    dsimp [P']; by_cases h : Even d <;> simp [banks,h] <;> assumption
  have hES' : E+q*q≤S' ∨ S'+L≤E := by
    dsimp [S']; by_cases h : Even d <;> simp [banks,h] <;> assumption
  have h3t : t.registers 3=P' := by simpa [environment,P'] using htr ⟨3,by omega⟩
  have h4t : t.registers 4=S' := by simpa [environment,S'] using htr ⟨4,by omega⟩
  let u := savedBanks t k P' S'
  have eu := saveBanks_correct (w:=w) (k:=k) (P:=P') (S:=S') t hk (by omega) (by omega) h3t h4t
  have hut : ∀ i, i<8 → u.registers (k+i)=context A (tensorStride q d) (A*q*tensorStride q d) (q^d) D E T i := by
    intro i hi
    change Function.update (Function.update t.registers (k+8) P') (k+9) S' (k+i)=_
    rw [Function.update_of_ne (show k+i≠k+9 by omega),Function.update_of_ne (show k+i≠k+8 by omega),protected_frame et hkw i]
    exact hctx i hi
  have h8u : u.registers (k+8)=P' := by simp [u,savedBanks,put]
  have h9u : u.registers (k+9)=S' := by simp [u,savedBanks,put]
  let v := patched u 5 (degreeValues (A*q^d) S' (q^d) D)
  have ev := degreeSetup_correct (w:=w) (k:=k) (N:=A*q^d) (S:=S') (Q:=q^d) (D:=D) u hk (by omega) (by omega) (by omega) hD
    (by simpa [context] using hut 7 (by omega)) h9u
    (by simpa [context] using hut 3 (by omega)) (by simpa [context] using hut 4 (by omega))
  obtain ⟨c2,t2,et2,hc2,ht20,ht2m,ht2f⟩:=DegreeFilter.command_correct (w:=w) (q:=q) (d:=d) (N:=A*q^d) (P:=S') (D:=D) v
    hq hqw (by omega) (by omega) hD
    (by simp [v,patched,degreeValues]) (by simp [v,patched,degreeValues])
    (by simp [v,patched,degreeValues]) (by simp [v,patched,degreeValues])
  have h2ctx : ∀ i, t2.registers (k+i)=u.registers (k+i) := by
    intro i
    rw [ht2f (k+i) (by omega) (by omega)]
    simp [v,patched,show ¬k+i<5 by omega]
  let u2 := patched t2 8 (tensorValues T (A*q*tensorStride q d) P' S' E (tensorStride q d) A)
  have eu2 := tensorSetup_correct (w:=w) (k:=k) (T:=T) (N:=A*q*tensorStride q d) (P:=P') (S:=S') (C:=E) (B:=tensorStride q d) (A:=A) t2 hk (by omega) hNw (by omega) (by omega) (by omega) hBw hAw
    (by simpa only [Nat.add_zero] using (h2ctx 0).trans (by simpa [context] using hut 0 (by omega)))
    ((h2ctx 1).trans (by simpa [context] using hut 1 (by omega)))
    ((h2ctx 2).trans (by simpa [context] using hut 2 (by omega)))
    ((h2ctx 5).trans (by simpa [context] using hut 5 (by omega)))
    ((h2ctx 6).trans (by simpa [context] using hut 6 (by omega)))
    (by rw [h2ctx,h8u]) (by rw [h2ctx,h9u])
  have hu2regs : ∀ a : Fin 8, u2.registers a.val=
      environment T (A*q*tensorStride q d) P' S' E (tensorStride q d) A 0 a := by
    intro a
    simp only [u2,patched,a.isLt,ite_eq_left,tensorValues_environment]
  have hu2x : ∀ i, i<A*q^d → u2.memory (S'+i)=some (filtered q d D (tensorValue T q q c d x) i) ∧
      filtered q d D (tensorValue T q q c d x) i<T := by
    intro i hi
    change t2.memory _=_ ∧ _
    rw [ht2m,DegreeFilter.memory_entry _ hi]
    change (if D<DigitSum.value q d (i%(q^d)) then some 0 else t.memory (S'+i))=_ ∧ _
    have hm := htm i hi
    by_cases hh : D<DigitSum.value q d (i%(q^d))
    · simp [filtered,hh,hT]
    · simpa [filtered,hh] using hm
  have hu2e : ∀ i, i<q*q → u2.memory (E+i)=some (e i) ∧ e i<T := by
    intro i hi
    change t2.memory _=_ ∧ _
    rw [ht2m,DegreeFilter.memory_outside _ (by omega : E+i<S' ∨ S'+A*q^d≤E+i)]
    change t.memory _=_ ∧ _
    rw [htf _ (by omega) (by omega)]
    exact he i hi
  obtain ⟨c3,z,ez,hc3,hzr,hzm,hzf⟩:=tensorCommand_correct u2
    (filtered q d D (tensorValue T q q c d x)) e hq hq0 hA hT hadd hmul
    (by simpa only [max_self] using hL) hLw hP' hS' hE hPS' hEP' hES' hu2regs hu2x hu2e
  have hbank : banks d P' S'=(P,S) := banks_twice d P S
  refine ⟨c1+(2+(5+(c2+(8+c3)))),z,Eval.seq et (Eval.seq eu (Eval.seq ev (Eval.seq et2 (Eval.seq eu2 ez)))),?_,?_,?_,?_⟩
  · nlinarith
  · simpa only [hbank,Prod.fst,Prod.snd] using hzr
  · simpa only [hbank,Prod.fst,Prod.snd] using hzm
  · intro a haP haS
    have hp : a<P' ∨ P'+L≤a := by
      dsimp [P']; by_cases h : Even d <;> simp [banks,h] <;> assumption
    have hs : a<S' ∨ S'+L≤a := by
      dsimp [S']; by_cases h : Even d <;> simp [banks,h] <;> assumption
    rw [hzf _ hp hs]
    change t2.memory a=s.memory a
    rw [ht2m,DegreeFilter.memory_outside _ (by omega : a<S' ∨ S'+A*q^d≤a)]
    exact htf a haP haS
end DeterministicThreeSum.Structured.Indexed.NewtonPass

end OAI
