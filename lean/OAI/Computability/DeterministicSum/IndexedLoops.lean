import Mathlib
import OAI.Computability.DeterministicSum.Expressions

namespace OAI

/-! Indexed kernels and memory-preserving iteration. -/

namespace DeterministicThreeSum.Structured
open Command

def written (initial : Data) (base : ℕ) (f : ℕ → ℕ) (k a : ℕ) : Option ℕ :=
  if base≤a ∧ a<base+k then some (f (a-base)) else initial.memory a

lemma written_next (initial : Data) (base : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    Function.update (written initial base f k) (base+k) (some (f k))=
      written initial base f (k+1) := by
  funext a
  by_cases ha : a=base+k
  · subst a; simp [written]
  · rw [Function.update_of_ne ha]
    unfold written
    have hh : (base≤a ∧ a<base+k) ↔ (base≤a ∧ a<base+(k+1)) := by omega
    simp only [hh]

lemma written_zero (initial : Data) (base : ℕ) (f : ℕ → ℕ) :
    written initial base f 0=initial.memory := by
  funext a
  simp [written]

lemma written_outside {initial : Data} {base k a : ℕ} {f : ℕ → ℕ}
    (ha : a<base ∨ base+k≤a) : written initial base f k a=initial.memory a := by
  simp only [written,ite_eq_right (by omega : ¬(base≤a ∧ a<base+k))]

def indexedLoop (index bound : ℕ) (body : Command) : Command :=
  .loop .lt (.register index) (.register bound)
    (.seq body (.atom (.binary index .add (.register index) (.literal 1))))

theorem indexedLoop_correct {w n index bound base K : ℕ}
    (hnw : n+1<wordModulus w) (_hne : index≠bound)
    (body : Command) (initial s : Data) (f : ℕ → ℕ) (keep : ℕ → Prop)
    (hkeep : keep bound) (hindex : ¬keep index)
    (hbound : s.registers bound=n) (hstart : s.registers index=0)
    (hm : s.memory=initial.memory)
    (stepProof : ∀ k t, k<n →
      (∀ r, keep r → t.registers r=s.registers r) → t.registers index=k →
      t.memory=written initial base f k →
      ∃ cost u, Eval w body t cost u ∧ cost≤K ∧
        (∀ r, keep r ∨ r=index → u.registers r=t.registers r) ∧
        u.memory=Function.update t.memory (base+k) (some (f k))) :
    ∃ cost t, Eval w (indexedLoop index bound body) s cost t ∧ cost≤(K+3)*n+1 ∧
      (∀ r, keep r → t.registers r=s.registers r) ∧ t.registers index=n ∧
      t.memory=written initial base f n := by
  let Inv : ℕ → Data → Prop := fun k t =>
    (∀ r, keep r → t.registers r=s.registers r) ∧ t.registers index=k ∧
      t.memory=written initial base f k
  have hyes : ∀ k t, k<n → Inv k t → test w t .lt (.register index) (.register bound)=true := by
    intro k t hk ht
    simp [test,operand_register,evalTest,ht.1 bound hkeep,hbound,ht.2.1,
      Nat.mod_eq_of_lt (by omega : n<wordModulus w),Nat.mod_eq_of_lt (by omega : k<wordModulus w),hk]
  have hno : ∀ t, Inv n t → test w t .lt (.register index) (.register bound)=false := by
    intro t ht
    simp [test,operand_register,evalTest,ht.1 bound hkeep,hbound,ht.2.1]
  have hb : ∀ k t, k<n → Inv k t → ∃ cost u,
      Eval w (.seq body (.atom (.binary index .add (.register index) (.literal 1)))) t cost u ∧
      cost≤K+1 ∧ Inv (k+1) u := by
    intro k t hk ht
    obtain ⟨cost,u,he,hc,hr,hu⟩ := stepProof k t hk ht.1 ht.2.1 ht.2.2
    have hi : u.registers index=k := (hr index (Or.inr rfl)).trans ht.2.1
    have einc:=eval_increment (w:=w) (s:=u) (r:=index) (by rw [hi]; omega)
    rw [hi] at einc
    refine ⟨cost+1,put u index (k+1),Eval.seq he einc,by omega,?_,?_,?_⟩
    · intro r hr'
      have hri : r≠index := by intro hh; subst r; exact hindex hr'
      simp only [put,Function.update_of_ne hri]
      exact (hr r (Or.inl hr')).trans (ht.1 r hr')
    · simp only [put,Function.update_self]
    · change u.memory=_
      rw [hu,ht.2.2,written_next]
  have hs : Inv 0 s := ⟨fun _ _ => rfl,hstart,by rwa [written_zero]⟩
  obtain ⟨cost,t,he,hc,ht⟩ := bounded_loop Inv hyes hno hb (i:=0) (by omega) hs
  exact ⟨cost,t,he,by simpa [Nat.add_assoc] using hc,ht⟩

end DeterministicThreeSum.Structured
namespace DeterministicThreeSum.Structured.Indexed
open Command

def Scalar.reads {m : ℕ} (env : Fin m → ℕ) : Scalar m → Finset ℕ
  | .literal _ => ∅
  | .input a => {a.value env}
  | .binary _ a b => a.reads env ∪ b.reads env
  | .branch x y a b => if x.value env<y.value env then a.reads env else b.reads env

lemma Scalar.memory_congr {m w T : ℕ} (e : Scalar m) (env : Fin m → ℕ)
    (mem mem' : ℕ → Option ℕ)
    (h : ∀ a∈e.reads env, mem a=mem' a) :
    (e.Valid w T env mem ↔ e.Valid w T env mem') ∧ e.value T env mem=e.value T env mem' := by
  induction e with
  | literal k => exact ⟨Iff.rfl,rfl⟩
  | input a =>
    have hh:=h (a.value env) (by simp [Scalar.reads])
    simp [Scalar.Valid,Scalar.value,hh]
  | binary op a b iha ihb =>
    obtain ⟨ha,ha'⟩:=iha (fun k hk => h k (by simp only [Scalar.reads,Finset.mem_union];exact Or.inl hk))
    obtain ⟨hb,hb'⟩:=ihb (fun k hk => h k (by simp only [Scalar.reads,Finset.mem_union];exact Or.inr hk))
    exact ⟨and_congr ha hb,by simp only [Scalar.value,ha',hb']⟩
  | branch x y a b iha ihb =>
    by_cases hh : x.value env<y.value env
    · have ih:=iha (by simpa only [Scalar.reads,ite_eq_left hh] using h)
      simpa only [Scalar.Valid,Scalar.value,ite_eq_left hh] using
        And.intro (and_congr Iff.rfl (and_congr Iff.rfl ih.1)) ih.2
    · have ih:=ihb (by simpa only [Scalar.reads,ite_eq_right hh] using h)
      simpa only [Scalar.Valid,Scalar.value,ite_eq_right hh] using
        And.intro (and_congr Iff.rfl (and_congr Iff.rfl ih.1)) ih.2

def kernelBody {m : ℕ} (index base : Fin m) (e : Scalar m) : Command :=
  .seq (e.compile m) (straight [.binary (m+1) .add (.register base.val) (.register index.val),
    .store (.register (m+1)) (.register m)])

def kernel {m : ℕ} (index bound base : Fin m) (e : Scalar m) : Command :=
  indexedLoop index.val bound.val (kernelBody index base e)

theorem kernel_correct {m w T N P : ℕ} (index bound base : Fin m) (e : Scalar m)
    (s : Data) (hm3 : 3 ≤ m) (hT : 0<T) (hadd : 2*T<wordModulus w)
    (hmul : T*T<wordModulus w) (hnw : N+1<wordModulus w)
    (hP : P+N<wordModulus w) (hib : index≠bound) (hip : index≠base)
    (hi2 : index.val≠2) (hbound : s.registers bound.val=N)
    (hbase : s.registers base.val=P) (hmod : s.registers 2=T)
    (hstart : s.registers index.val=0)
    (hv : ∀ i, i<N → e.Valid w T (Function.update (fun a : Fin m => s.registers a.val) index i) s.memory)
    (hdis : ∀ i, i<N → ∀ a∈e.reads (Function.update (fun a : Fin m => s.registers a.val) index i),
      a<P ∨ P+N≤a) :
    ∃ c t, Eval w (kernel index bound base e) s c t ∧ c≤(e.cost+5)*N+1 ∧
      (∀ r, r< m → r≠index.val → t.registers r=s.registers r) ∧
      t.registers index.val=N ∧
      t.memory=written s P
        (fun i => e.value T (Function.update (fun a : Fin m => s.registers a.val) index i) s.memory) N := by
  let env : ℕ → Fin m → ℕ := fun i => Function.update (fun a : Fin m => s.registers a.val) index i
  let f : ℕ → ℕ := fun i => e.value T (env i) s.memory
  let keep : ℕ → Prop := fun r => r< m ∧ r≠index.val
  have hkeep : keep bound.val := ⟨bound.isLt,fun h => hib (Fin.ext h.symm)⟩
  have hnot : ¬keep index.val := by simp [keep]
  have stepProof : ∀ i u, i<N →
      (∀ r, keep r → u.registers r=s.registers r) → u.registers index.val=i →
      u.memory=written s P f i →
      ∃ c v, Eval w (kernelBody index base e) u c v ∧ c≤e.cost+2 ∧
        (∀ r, keep r ∨ r=index.val → v.registers r=u.registers r) ∧
        v.memory=Function.update u.memory (P+i) (some (f i)) := by
    intro i u hi hu hindex hmem
    have hparams : ∀ a : Fin m, u.registers a.val=env i a := by
      intro a
      by_cases h : a=index
      · subst a; simpa [env] using hindex
      · simpa [env,h] using hu a.val ⟨a.isLt,fun hh => h (Fin.ext hh)⟩
    have hmod' : u.registers 2=T := (hu 2 ⟨by omega,Ne.symm hi2⟩).trans hmod
    have heq : ∀ a∈e.reads (env i), u.memory a=s.memory a := by
      intro a ha
      rw [hmem]
      exact written_outside (by have hh:=hdis i hi a ha;omega)
    obtain ⟨heqValid,heqVal⟩:=e.memory_congr (w:=w) (T:=T) (env i) u.memory s.memory heq
    obtain ⟨c,v,he,hc,hvm,hvr,hvf⟩:=e.compile_correct (env i) u.memory u le_rfl hm3 hT hadd hmul
      hparams hmod' rfl (heqValid.mpr (hv i hi))
    have hval : v.registers m=f i := hvr.trans heqVal
    have hidx : v.registers index.val=i := (hvf _ index.isLt).trans hindex
    have hbas : v.registers base.val=P := (hvf _ base.isLt).trans
      ((hu _ ⟨base.isLt,fun h => hip (Fin.ext h.symm)⟩).trans hbase)
    have hfv : f i<wordModulus w := lt_trans (e.value_lt (env i) s.memory hT (hv i hi)) (by omega)
    let z : Data := {put v (m+1) (P+i) with memory:=Function.update v.memory (P+i) (some (f i))}
    have hz : Eval w (straight [.binary (m+1) .add (.register base.val) (.register index.val),
      .store (.register (m+1)) (.register m)]) v 2 z := by
      apply straight_correct
      simp [execStraight,Atom.eval,evalBinOp,operand_register,put,z,hidx,hbas,hval,
        Nat.mod_eq_of_lt (show P<wordModulus w by omega),Nat.mod_eq_of_lt (show i<wordModulus w by omega),
        Nat.mod_eq_of_lt (show P+i<wordModulus w by omega),Nat.mod_eq_of_lt hfv]
    refine ⟨c+2,z,Eval.seq he hz,by omega,?_,?_⟩
    · intro r hr
      have hr' : r< m := by rcases hr with hr|rfl;exact hr.1;exact index.isLt
      simp only [z,put,Function.update_of_ne (show r≠m+1 by omega)]
      exact hvf r hr'
    · change Function.update v.memory (P+i) (some (f i))=_
      rw [hvm]
  obtain ⟨c,t,he,hc,hr,ht,hm⟩:=indexedLoop_correct (w:=w) (n:=N) (base:=P) (K:=e.cost+2)
    hnw (fun h => hib (Fin.ext h)) (kernelBody index base e) s s f keep hkeep hnot
    hbound hstart rfl stepProof
  exact ⟨c,t,he,by simpa only [Nat.add_assoc] using hc,fun r hr' hi => hr r ⟨hr',hi⟩,ht,hm⟩

end DeterministicThreeSum.Structured.Indexed

end OAI
