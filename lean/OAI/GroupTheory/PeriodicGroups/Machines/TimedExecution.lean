import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.ProgramFixedPoint

namespace OAI

universe u v w
namespace SourceBurnside.OneTape
open Tableau
variable {Γ Q : Type*}

structure Coding (Γ Q : Type*) where
  bits : ℕ
  positive : 0<bits
  encode : Label Γ Q → (Fin bits → Bool)
  decode : (Fin bits → Bool) → Label Γ Q
  decode_encode : ∀ a, decode (encode a)=a

namespace Coding
section
variable [Fintype Γ] [Fintype Q]
noncomputable def oneHotEncode (a : Label Γ Q) : Fin (Fintype.card (Label Γ Q)) → Bool :=
  fun i => decide (Fintype.equivFin (Label Γ Q) a=i)

lemma oneHotEncode_injective : Function.Injective (oneHotEncode (Γ:=Γ) (Q:=Q)) := by
  intro a b he
  have hh := congrFun he (Fintype.equivFin (Label Γ Q) a)
  have hb : Fintype.equivFin (Label Γ Q) b=Fintype.equivFin (Label Γ Q) a := by
    exact of_decide_eq_true (by simpa only [oneHotEncode,decide_true] using hh.symm)
  exact ((Fintype.equivFin (Label Γ Q)).injective hb).symm

noncomputable def oneHot (blank : Γ) : Coding Γ Q where
  bits := Fintype.card (Label Γ Q)
  positive := Fintype.card_pos_iff.mpr ⟨⟨blank,false,none⟩⟩
  encode := oneHotEncode
  decode v := if hv : ∃ a, oneHotEncode a=v then Classical.choose hv else ⟨blank,false,none⟩
  decode_encode a := by
    rw [dite_eq_left (show ∃ b, oneHotEncode b=oneHotEncode a from ⟨a,rfl⟩)]
    exact oneHotEncode_injective (Classical.choose_spec
      (show ∃ b, oneHotEncode b=oneHotEncode a from ⟨a,rfl⟩))
end

variable (K : Coding Γ Q)
lemma encode_injective : Function.Injective K.encode := Function.LeftInverse.injective K.decode_encode

def transition (δ : Q → Γ → Command Γ Q) (v : Fin (3*K.bits) → Bool) : Fin K.bits → Bool :=
  let extract := fun b : Fin 3 => K.decode (fun r => v (finProdFinEquiv (b,r)))
  K.encode (localStep δ (extract 0) (extract 1) (extract 2))

structure Realization (δ : Q → Γ → Command Γ Q) where
  gates : ℕ
  circuit : Tableau.Circuit (3*K.bits) gates
  output : Fin K.bits → Tableau.Wire (3*K.bits+gates)
  correct : ∀ v r, (output r).eval (circuit.evaluate v)=K.transition δ v r

noncomputable def realization (δ : Q → Γ → Command Γ Q) : K.Realization δ :=
  Classical.choice (by
    obtain ⟨g,c,out,hc⟩ := Tableau.exists_nand_circuit (K.transition δ)
    exact ⟨⟨g,c,out,hc⟩⟩)

def trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (origin : ℕ)
    (t j : ℕ) : Fin K.bits → Bool := K.encode ((run δ C t).cell ((j:ℤ)-(origin:ℤ)))

theorem local_trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (origin t j : ℕ) :
    K.transition δ (Rectangle.neighborhood (K.trace δ C origin t) j)=
      K.trace δ C origin (t+1) (j+1) := by
  have hex (b : Fin 3) : K.decode (fun r =>
      Rectangle.neighborhood (K.trace δ C origin t) j (finProdFinEquiv (b,r)))=
      (run δ C t).cell ((j+b.val:ℕ)- (origin:ℤ)) := by
    simp only [Rectangle.neighborhood,Equiv.symm_apply_apply,trace,K.decode_encode]
  dsimp only [transition]
  rw [hex 0,hex 1,hex 2]
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two]
  have h₁ : ((j+1:ℕ):ℤ)-(origin:ℤ)-1=(j:ℤ)-(origin:ℤ) := by push_cast; ring
  have h₂ : ((j+1:ℕ):ℤ)-(origin:ℤ)+1=((j+2:ℕ):ℤ)-(origin:ℤ) := by push_cast; ring
  have he := local_cell δ (run δ C t) (((j+1:ℕ):ℤ)-(origin:ℤ))
  rw [h₁,h₂] at he
  simpa only [Nat.add_zero,trace,run] using congrArg K.encode he
end Coding

lemma far_cell (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (blank : Γ)
    (hp : C.position=0) (t : ℕ) (j : ℤ) (hj : j< -(t:ℤ) ∨ (t:ℤ)<j)
    (hb : C.tape j=blank) : (run δ C t).cell j=⟨blank,false,none⟩ := by
  have hpos := run_position_bound δ C t
  rw [hp] at hpos
  have h0 : j≠0 := by omega
  have hne : j≠(run δ C t).position := by omega
  have htape : (run δ C t).tape j=C.tape j := run_tape_untouched δ C t j (by
    intro s hs
    have hh := run_position_bound δ C s
    rw [hp] at hh
    omega)
  simp [Config.cell,htape,hb,h0,hne]

namespace Coding
variable (K : Coding Γ Q)

lemma boundary_trace (δ : Q → Γ → Command Γ Q) (C : Config Γ Q) (blank : Γ)
    (T : ℕ) (hT : 0<T) (hp : C.position=0)
    (hl : C.tape (-(2*(T:ℤ)))=blank) (hr : C.tape (2*(T:ℤ)-1)=blank)
    (t : ℕ) (ht : t<T) (j : ℕ) (hj : j=0 ∨ j+1=4*T) :
    K.trace δ C (2*T) t j=K.encode ⟨blank,false,none⟩ := by
  unfold trace
  apply congrArg K.encode
  rcases hj with rfl|hj
  · apply far_cell δ C blank hp t _
    · left; push_cast; omega
    · simpa using hl
  · have he : (j:ℤ)-((2*T:ℕ):ℤ)=2*(T:ℤ)-1 := by push_cast; omega
    rw [he]
    exact far_cell δ C blank hp t _ (Or.inr (by omega)) hr

theorem rectangle_valid (δ : Q → Γ → Command Γ Q) (M : K.Realization δ)
    (C : Config Γ Q) (blank : Γ) (T : ℕ) (hT : 0<T) (hp : C.position=0)
    (hl : C.tape (-(2*(T:ℤ)))=blank) (hr : C.tape (2*(T:ℤ)-1)=blank) :
    Rectangle.Valid M.circuit M.output T (4*T) (K.encode ⟨blank,false,none⟩)
      (K.trace δ C (2*T) 0) (K.trace δ C (2*T))
      (fun t j v => M.circuit.evaluate (Rectangle.neighborhood (K.trace δ C (2*T) t) j)
        (Fin.natAdd (3*K.bits) v)) := by
  refine ⟨fun _ _ => rfl,?_,?_,?_⟩
  · intro t ht j hj he
    exact K.boundary_trace δ C blank T hT hp hl hr (t+1) ht j he
  · intro t ht j hj
    rw [Rectangle.assignment_evaluate]
    exact M.circuit.evaluate_satisfies _
  · intro t ht j hj r
    rw [Rectangle.assignment_evaluate,M.correct]
    exact (congrFun (K.local_trace δ C (2*T) t j) r).symm

theorem rectangle_run (δ : Q → Γ → Command Γ Q) (M : K.Realization δ)
    (C : Config Γ Q) (blank : Γ) (T : ℕ) (hT : 0<T) (hp : C.position=0)
    (hl : C.tape (-(2*(T:ℤ)))=blank) (hr : C.tape (2*(T:ℤ)-1)=blank)
    (t : ℕ) (ht : t<T) (j : ℕ) (hj : j<4*T) :
    Rectangle.run M.circuit M.output (4*T) (K.encode ⟨blank,false,none⟩)
      (K.trace δ C (2*T) 0) t j=K.trace δ C (2*T) t j :=
  (Rectangle.valid_run M.circuit M.output
    (K.rectangle_valid δ M C blank T hT hp hl hr) t ht j hj).symm

end Coding
end SourceBurnside.OneTape

namespace SourceBurnside.Addressable.InputBit
variable {q : ℕ}

def mapBool (f : Bool → Bool) : InputBit q → InputBit q
  | .fixed b => .fixed (f b)
  | .input p neg => match f false,f true with
    | false,false => .fixed false
    | false,true => .input p neg
    | true,false => .input p (!neg)
    | true,true => .fixed true

lemma eval_mapBool (f : Bool → Bool) (a : InputBit q) (v : FiniteTable.Address q → Bool) :
    (a.mapBool f).eval v=f (a.eval v) := by
  cases a with
  | fixed b => rfl
  | input p neg =>
    cases h0 : f false <;> cases h1 : f true <;> cases hv : v (dataAddress p) <;> cases neg <;>
      simp [mapBool,eval,h0,h1,hv]
end SourceBurnside.Addressable.InputBit

namespace SourceBurnside.OneTape
section
open Tableau Addressable
variable {Γ Q : Type*} {q : ℕ}

structure Input where
  content : List (InputBit q)
  blank : Γ
  origin : Γ
  bitSymbol : Bool → Γ
  start : Q

namespace Input
variable (A : Input (Γ:=Γ) (Q:=Q) (q:=q))
def symbol (v : FiniteTable.Address q → Bool) (j : ℤ) : Γ :=
  if j=0 then A.origin else
    if hj : 0<j.toNat ∧ j.toNat≤A.content.length then
      A.bitSymbol ((A.content[j.toNat-1]'(by omega)).eval v)
    else A.blank

def config (v : FiniteTable.Address q → Bool) : Config Γ Q := ⟨0,A.start,A.symbol v⟩

def reading (K : Coding Γ Q) (j : ℤ) (r : Fin K.bits) : InputBit q :=
  if j=0 then .fixed (K.encode ⟨A.origin,true,some A.start⟩ r) else
    if hj : 0<j.toNat ∧ j.toNat≤A.content.length then
      (A.content[j.toNat-1]'(by omega)).mapBool
        (fun b => K.encode ⟨A.bitSymbol b,false,none⟩ r)
    else .fixed (K.encode ⟨A.blank,false,none⟩ r)

lemma reading_eval (K : Coding Γ Q) (v : FiniteTable.Address q → Bool) (j : ℤ) (r : Fin K.bits) :
    (A.reading K j r).eval v=K.encode ((A.config v).cell j) r := by
  by_cases h0 : j=0
  · subst j
    simp only [reading,ite_true,InputBit.eval,config,Config.cell,symbol,decide_true]
  · by_cases hh : 0<j.toNat ∧ j.toNat≤A.content.length
    · simp [reading,h0,hh,InputBit.eval_mapBool,config,Config.cell,symbol]
    · have hh' : ¬ (0 < j ∧ j ≤ (A.content.length : ℤ)) := by omega
      simp [reading,h0,hh',InputBit.eval,config,Config.cell,symbol]

lemma left_blank (v : FiniteTable.Address q → Bool) (T : ℕ) (hT : 0<T) :
    (A.config v).tape (-(2*(T:ℤ)))=A.blank := by
  unfold config symbol
  simp only
  rw [ite_eq_right (by omega)]
  rw [dite_eq_right (by omega)]

lemma right_blank (v : FiniteTable.Address q → Bool) (T : ℕ) (hT : 0<T)
    (hl : A.content.length<T) : (A.config v).tape (2*(T:ℤ)-1)=A.blank := by
  unfold config symbol
  simp only
  rw [ite_eq_right (by omega)]
  rw [dite_eq_right (by omega)]

def initialBits (K : Coding Γ Q) (T : ℕ) (j : Fin (4*T)) (r : Fin K.bits) : InputBit q :=
  A.reading K ((j.val:ℤ)-((2*T:ℕ):ℤ)) r

lemma initialBits_eval (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q) (T : ℕ)
    (v : FiniteTable.Address q → Bool) (j : Fin (4*T)) (r : Fin K.bits) :
    (A.initialBits K T j r).eval v=K.trace δ (A.config v) (2*T) 0 j.val r :=
  A.reading_eval K v _ r

theorem addressed_rectangle (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q)
    (M : K.Realization δ) (T : ℕ) (hT : 0<T) (hl : A.content.length<T)
    (L : Addressable.Layout q K.bits M.gates T (4*T)) (v : FiniteTable.Address q → Bool) :
    Rectangle.Valid M.circuit M.output T (4*T) (K.encode ⟨A.blank,false,none⟩)
      (L.inputRow (A.initialBits K T) v) (K.trace δ (A.config v) (2*T))
      (fun t j r => M.circuit.evaluate (Rectangle.neighborhood (K.trace δ (A.config v) (2*T) t) j)
        (Fin.natAdd (3*K.bits) r)) := by
  have hv := K.rectangle_valid δ M (A.config v) A.blank T hT rfl
    (A.left_blank v T hT) (A.right_blank v T hT hl)
  refine ⟨?_,hv.2⟩
  intro j hj
  funext r
  rw [L.inputRow_at _ v hj]
  exact (A.initialBits_eval K δ T v ⟨j,hj⟩ r).symm

theorem certificate_machine_iff (K : Coding Γ Q) (δ : Q → Γ → Command Γ Q)
    (M : K.Realization δ) (T : ℕ) (hT : 0<T) (hl : A.content.length<T)
    (L : Addressable.Layout q K.bits M.gates T (4*T)) (ho : L.origin.val=2*T)
    (accept : Label Γ Q) (data : DataAddress q → Bool) :
    (∃ cert : Fin q → Bool, ∀ i,
      (L.clauseAt M.circuit M.output (A.initialBits K T)
        (K.encode ⟨A.blank,false,none⟩) (K.encode accept) i).Holds (Addressable.Layout.assemble data cert)) ↔
    (run δ (A.config (Addressable.Layout.assemble data (fun _ => false))) (T-1)).cell 0=accept := by
  rw [L.certificate_iff]
  have hv := A.addressed_rectangle K δ M T hT hl L
    (Addressable.Layout.assemble data (fun _ => false))
  rw [← Rectangle.valid_run M.circuit M.output hv (T-1) (by omega) L.origin.val L.origin.isLt]
  rw [ho]
  simp only [Coding.trace,sub_self]
  exact K.encode_injective.eq_iff

end Input
end
variable {Γ Q : Type*}

def Frozen (δ : Q → Γ → Command Γ Q) (q : Q) : Prop :=
  ∀ a, δ q a = ⟨a,q,Move.stay⟩

lemma step_of_frozen (δ : Q → Γ → Command Γ Q) (q : Q) (hq : Frozen δ q)
    (C : Config Γ Q) (hs : C.state=q) : step δ C=C := by
  cases C with
  | mk p s tape =>
    dsimp at hs
    subst s
    simp [step,hq (tape p),Move.shift]

lemma run_of_step_eq (δ : Q → Γ → Command Γ Q) (C : Config Γ Q)
    (h : step δ C=C) (t : ℕ) : run δ C t=C := by
  induction t with
  | zero => rfl
  | succ t hh => simp [run,hh,h]

lemma run_eq_of_frozen (δ : Q → Γ → Command Γ Q) (q : Q) (hq : Frozen δ q)
    (C : Config Γ Q) (s t : ℕ) (hst : s≤t) (hs : (run δ C s).state=q) :
    run δ C t=run δ C s := by
  rw [show t=s+(t-s) by omega,run_from]
  exact run_of_step_eq δ _ (step_of_frozen δ q hq _ hs) _

theorem final_accept_iff (δ : Q → Γ → Command Γ Q) (q : Q) (hq : Frozen δ q)
    (C : Config Γ Q) (T : ℕ) (hT : 0<T) (a : Label Γ Q) (ha : a.head=some q) :
    (run δ C (T-1)).cell 0=a ↔ ∃ s<T, (run δ C s).cell 0=a := by
  constructor
  · intro hh
    exact ⟨T-1,by omega,hh⟩
  · rintro ⟨s,hs,hc⟩
    have he := congrArg Label.head hc
    rw [ha] at he
    have hstate : (run δ C s).state=q := by
      dsimp [Config.cell] at he
      split at he
      · exact Option.some.inj he
      · contradiction
    rw [run_eq_of_frozen δ q hq C s (T-1) (by omega) hstate]
    exact hc

end SourceBurnside.OneTape

namespace SourceBurnside.ExponentialThreshold
open Filter Asymptotics
lemma polynomial_lt (C k : ℕ) : ∃n0 : ℕ, ∀n≥n0,C*n^k < 2^n := by
  have H : (fun n : ℕ => (C:ℝ)*(n:ℝ)^k) =o[atTop] (fun n => (2:ℝ)^n) :=
    (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) k (by norm_num : (1:ℝ)<2)).const_mul_left C
  have he := H.eventuallyLT_norm_of_eventually_pos (Filter.Eventually.of_forall (fun n => norm_pos_iff.mpr (pow_ne_zero n (by norm_num : (2:ℝ)≠0))))
  obtain ⟨n0,h0⟩ := Filter.eventually_atTop.mp he
  refine ⟨n0,?_⟩
  intro n hn
  have HH := h0 n hn
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(C:ℝ)*(n:ℝ)^k),
    abs_of_nonneg (by positivity : 0≤(2:ℝ)^n)] at HH
  exact_mod_cast HH
lemma scaled (C k a : ℕ) (ha : 0<a) : ∃h0 : ℕ, ∀h≥h0,C*h^k < 2^(h/a) := by
  obtain ⟨n0,h0⟩ := polynomial_lt (C*(2*a)^k) k
  refine ⟨a*(n0+1),?_⟩
  intro h hh
  have hd : n0+1 ≤ h/a := (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hh)
  have hbound : h ≤ 2*a*(h/a) := by
    have hr := Nat.mod_lt h ha
    have hre := Nat.mod_add_div h a
    have hf : a ≤ a*(h/a) := Nat.le_mul_of_pos_right a (by omega)
    nlinarith
  calc
    C*h^k ≤ C*(2*a*(h/a))^k := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbound k)
    _ = C*(2*a)^k*(h/a)^k := by ring
    _ < 2^(h/a) := h0 _ (by omega)
end SourceBurnside.ExponentialThreshold

namespace SourceBurnside.RawFit
open ExponentialThreshold
lemma eventually_fits (β g D n : ℕ) : ∃h0 : ℕ, ∀h≥h0,Fits β g D h n := by
  let B := 25*β+12*g+1
  let A := 3*n+2*D+12+200000*D
  obtain ⟨u,hu⟩ := scaled (8*A) 1 5 (by omega)
  obtain ⟨v,hv⟩ := scaled (10000*D) 1 1 (by omega)
  obtain ⟨w,hw⟩ := scaled B 0 5 (by omega)
  refine ⟨max 4 (max u (max v w)),?_⟩
  intro h hh
  have h4 : 4≤h := (le_max_left _ _).trans hh
  have h1 : 1≤h := by omega
  have HH : u≤h ∧ v≤h ∧ w≤h := by omega
  have hT : 1 ≤ 2^(h/5) := Nat.one_le_pow _ _ (by omega)
  have hBn : B ≤ 2^(h/5) := by have := hw h HH.2.2;simp only [pow_zero,mul_one] at this;omega
  have hBeq : (2:ℕ)^(h/5)*(2^(h/5))^2=2^(3*(h/5)) := by rw [←pow_mul,←pow_add];congr 1;omega
  have hQ : B*(2^(h/5))^2 ≤ 2^h := by
    calc
      B*(2^(h/5))^2 ≤ (2^(h/5))*(2^(h/5))^2 := Nat.mul_le_mul_right _ hBn
      _ = 2^(3*(h/5)) := hBeq
      _ ≤ 2^h := Nat.pow_le_pow_right (by omega) (by have := Nat.div_mul_le_self h 5;omega)
  have hN : n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) ≤ A*h := by
    have hn := InitialFormula.binSize_le_self n
    have hdh := InitialFormula.binSize_le_self (D*h)
    have hc := Nat.mul_le_mul_left (3*n+12) h1
    unfold A
    nlinarith
  have hi : n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) < 2^(h/5)/4 := by
    have H := hu h HH.1
    simp only [pow_one] at H
    have Hextra : (n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h))+1)*4 ≤ 2^(h/5) := by

      nlinarith only [hN,H]
    exact (Nat.lt_div_iff_mul_lt (by omega)).mpr (by omega)
  unfold Fits
  refine ⟨by omega,?_,?_,?_,?_,?_,hi⟩
  · have H : 2^4 ≤ 2^(2*h) := Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at H ⊢;omega
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · have H := hv h HH.2.1
    simp only [pow_one,Nat.div_one] at H
    nlinarith
  · have ht0 : 4*2^(h/5)-2 ≤ 4*2^(h/5) := Nat.sub_le _ _
    have ht1 : 2^(h/5)-1 ≤ 2^(h/5) := Nat.sub_le _ _
    have hm := Nat.mul_le_mul ht0 ht1
    have hm' := Nat.mul_le_mul_left g hm
    change _ ≤ _
    unfold B at hQ
    nlinarith only [hQ,hm']
  · have ht0 : 4*2^(h/5)-2 ≤ 4*2^(h/5) := Nat.sub_le _ _
    have ht1 : 2^(h/5)-1 ≤ 2^(h/5) := Nat.sub_le _ _
    have ht2 : 2^(h/5) ≤ (2^(h/5))^2 := by nlinarith
    have hm := Nat.mul_le_mul ht0 ht1
    have hm' := Nat.mul_le_mul_left (3*g+2*β) hm
    have hβ := Nat.mul_le_mul_left (10*β) ht2
    have hβ' := Nat.mul_le_mul_left β (show 1≤(2^(h/5))^2 by nlinarith)
    have hsm := Nat.mul_le_mul_left (2*β) ht1
    unfold B at hQ
    nlinarith only [hQ,hm',hβ,hβ',hsm]
end SourceBurnside.RawFit

namespace SourceBurnside.SourceMachine
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open TimedTape

opaque coding : OneTape.Coding Γ Q := OneTape.Coding.oneHot blank
opaque localCircuit : coding.Realization δ := coding.realization δ
abbrev β := coding.bits
abbrev g := localCircuit.gates
def blankBits := coding.encode ⟨blank,false,none⟩
def initialBits := coding.encode ⟨origin,true,some initialState⟩
def acceptBits := coding.encode (output true)
def bitEncoding (b : Bool) := coding.encode ⟨bitSymbol b,false,none⟩
def body (D : ℕ) : Formula (Fin 7) :=
  RawFit.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding
lemma bit_positive : 0<β := coding.positive

theorem timed_selfpoint (D : ℕ) (_hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ), 0<h0 ∧ ∀h≥h0,
      RawFit.Fits β g D h (WrappedInput.specialize t t).length ∧
      ∀(l : ℕ), l≤10 → ∀(z : Bool) (data : List Bool), data.length≤200000*(D*h) →
        ∃b : Bool,
          Add.bit b=(body D).eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) (D*h) l z data) ∧
          (OneTape.run δ (StackMachine.encode (start
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request (D*h) l z data))))
            (2^(h/5)-1)).cell 0=output b := by
  obtain ⟨t,C,hC⟩ := TimedTape.source_predicate β g D localCircuit.circuit localCircuit.output
    blankBits initialBits acceptBits bitEncoding
  let A := 200001*D+11
  obtain ⟨u,hu⟩ := ExponentialThreshold.scaled (C*A^8) 8 5 (by omega)
  obtain ⟨v,hv⟩ := RawFit.eventually_fits β g D (WrappedInput.specialize t t).length
  refine ⟨t,max 1 (max u v),by omega,?_⟩
  intro h hh
  have h1 : 1≤h := by omega
  have hU : u≤h := by omega
  have hV : v≤h := by omega
  refine ⟨hv h hV,?_⟩
  intro l hl z data hd
  obtain ⟨N,b,hN,hb,HC⟩ := hC (D*h) l z data
  refine ⟨b,hb,HC _ ?_⟩
  have hsz : RawTimeBound.size (D*h) l data ≤ A*h := by
    have H := Nat.mul_le_mul_left 11 h1
    unfold RawTimeBound.size A
    nlinarith only [H,hl,hd]
  have hn : N < 2^(h/5) := by
    calc
      N ≤ C*(RawTimeBound.size (D*h) l data)^8 := hN
      _ ≤ C*(A*h)^8 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsz 8)
      _ = C*A^8*h^8 := by ring
      _ < 2^(h/5) := hu h hU
  omega
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.TimedTape
noncomputable section
open Addressable
variable {q : ℕ}
abbrev addressedInput (content : List (InputBit q)) : OneTape.Input (Γ:=Γ) (Q:=Q) (q:=q) :=
  ⟨content,blank,origin,bitSymbol,initialState⟩
lemma initial_store (x : List Bool) (k : SK) :
    (start x).store k=if k=.reg LiteralCompiler.src then x.map UniversalStack.Token.bit else [] := by
  cases k with
  | reg k =>
    by_cases hh : k=LiteralCompiler.src
    · subst k;simp [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs]
    · simp [start,WrappedInput.config,UniversalStack.config,UniversalInput.inputRegs,hh]
  | front => rfl
  | back => rfl
  | pc => rfl
lemma raw_symbol_zero (x : List Bool) : StackMachine.tape (start x).store 0=origin := rfl
lemma raw_symbol_pos (x : List Bool) (j : ℤ) (hj : 0<j) (hx : j.toNat-1<x.length) :
    StackMachine.tape (start x).store j=bitSymbol (x[j.toNat-1]) := by
  apply congrArg₂ StackMachine.Symbol.mk
  · simp [ne_of_gt hj]
  · funext k
    simp only [ite_eq_left hj,initial_store]
    by_cases hk : k=.reg LiteralCompiler.src
    · simp [hk,List.getElem?_eq_getElem hx]
    · simp [hk]
lemma raw_symbol_far (x : List Bool) (j : ℤ) (hj : j≠0) (hx : ¬(0<j ∧ j.toNat-1<x.length)) :
    StackMachine.tape (start x).store j=blank := by
  apply congrArg₂ StackMachine.Symbol.mk
  · simp [hj]
  · funext k
    by_cases hp : 0<j
    · have hn : x.length≤j.toNat-1 := by omega
      simp only [ite_eq_left hp,initial_store]
      split_ifs <;> simp [List.getElem?_eq_none hn]
    · simp [hp]
lemma addressed_config (content : List (InputBit q)) (v : FiniteTable.Address q → Bool) :
    (addressedInput content).config v=StackMachine.encode (start (content.map (fun b => b.eval v))) := by
  change OneTape.Config.mk 0 initialState _=OneTape.Config.mk 0 initialState _
  congr 1
  funext j
  by_cases h0 : j=0
  · subst j;simp [OneTape.Input.symbol,raw_symbol_zero]
  · by_cases hp : 0<j.toNat ∧ j.toNat≤content.length
    · have hj : 0<j := by omega
      have hx : j.toNat-1<(content.map (fun b => b.eval v)).length := by simp only [List.length_map];omega
      rw [raw_symbol_pos _ j hj hx]
      simp [OneTape.Input.symbol,h0,hp]
    · rw [raw_symbol_far]
      · dsimp only [OneTape.Input.symbol,addressedInput]; rw [ite_eq_right h0,dite_eq_right hp]
      · exact h0
      · simp only [List.length_map]
        omega
end
end SourceBurnside.TimedTape

namespace SourceBurnside.SourceMachine
noncomputable section
section
open TimedTape Addressable
variable {q H l : ℕ}
def candidateBits (data : DataAddress q → Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) : List Bool :=
  (InitialFormula.inputData (10000*H) l Z hd hdq hl hl10).map
    (fun b => b.eval (Layout.assemble data (fun _ => false)))
lemma candidate_length (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (candidateBits data Z hd hdq hl hl10).length=(if Z then l*(10000*H) else 2*(l*(10000*H))) := by
  simp [candidateBits,InitialFormula.inputData]
lemma candidate_length_le (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (candidateBits data Z hd hdq hl hl10).length≤200000*H := by
  rw [candidate_length]
  cases Z <;> simp <;> nlinarith
lemma source_input_eval (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a H l Z hd hdq hl hl10).map
      (fun b => b.eval (Layout.assemble data (fun _ => false)))=
    WrappedInput.envelope a (RawHeader.request H l Z (candidateBits data Z hd hdq hl hl10)) := by
  simp [InitialFormula.sourceInput,List.map_append,List.map_map,InputBit.eval,WrappedInput.envelope,
    RawHeader.request,candidateBits,List.append_assoc,Function.comp_def]
lemma small_arity (l : ℕ) (hl : l≤10) : InitialFormula.binSize l≤4 := by
  interval_cases l <;> decide
lemma source_input_length (a : List Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a H l Z hd hdq hl hl10).length≤
      a.length+2*InitialFormula.binSize a.length+2*InitialFormula.binSize H+12+200000*H := by
  have Hl := small_arity l hl10
  have Hdata : (InitialFormula.inputData (10000*H) l Z hd hdq hl hl10).length≤200000*H := by
    simpa only [candidateBits,List.length_map] using
      candidate_length_le (fun _ => false) Z hd hdq hl hl10
  simp only [InitialFormula.sourceInput,List.length_append,List.length_map,List.length_cons,List.length_nil,
    InitialFormula.enc_length]
  omega
lemma source_config (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    (addressedInput (InitialFormula.sourceInput a H l Z hd hdq hl hl10)).config
      (Layout.assemble data (fun _ => false))=
      StackMachine.encode (start (WrappedInput.envelope a (RawHeader.request H l Z
        (candidateBits data Z hd hdq hl hl10)))) := by
  rw [addressed_config,source_input_eval]
def layout (h n D : ℕ) (fit : RawFit.Fits β g D h n) : Layout (2^h) β g (2^(h/5)) (4*2^(h/5)) where
  bit_pos := bit_positive
  time_pos := Nat.pow_pos (by omega)
  width_ge := by have := Nat.one_le_pow (h/5) 2 (by omega);omega
  certificate_fit := fit.2.2.2.2.1
  clause_fit := fit.2.2.2.2.2.1
  origin := ⟨2*2^(h/5),by have := Nat.pow_pos (n:=h/5) (by omega : 0<2);omega⟩
lemma layout_origin (h n D : ℕ) (fit : RawFit.Fits β g D h n) : (layout h n D fit).origin.val=2*2^(h/5) := rfl
lemma input_short (a : List Bool) (h D l : ℕ) (Z : Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (hl : 0<l) (hl10 : l≤10) :
    (InitialFormula.sourceInput a (D*h) l Z hd fit.2.2.2.1 hl hl10).length<2^(h/5) := by
  have H := source_input_length a Z hd fit.2.2.2.1 hl hl10
  have Hfit := fit.2.2.2.2.2.2
  have Hmono := Nat.div_le_self (2^(h/5)) 4
  nlinarith
end

open TimedTape Addressable Structured Structured.Binary

theorem tableau_selfpoint (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 0<h0), ∀(h : ℕ) (hh : h0≤h),
      ∃fit : RawFit.Fits β g D h (WrappedInput.specialize t t).length,
      ∀(l : ℕ) (hl : 0<l) (hl10 : l≤10) (z : Bool) (data : DataAddress (2^h)→Bool),
      let a := WrappedInput.specialize t t
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (lt_of_lt_of_le h0pos hh))
      let raw := candidateBits data z hd fit.2.2.2.1 hl hl10
      let input := addressedInput (InitialFormula.sourceInput a (D*h) l z hd fit.2.2.2.1 hl hl10)
      (∃ cert : Fin (2^h)→Bool, ∀i,
        ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
          (input.initialBits coding (2^(h/5))) blankBits acceptBits i).Holds
            (Layout.assemble data cert)) ↔
      (body D).eval (RawPreparedInputs.semantic a (D*h) l z raw)=1 := by
  obtain ⟨t,h0,h0pos,H⟩ := timed_selfpoint D hD
  refine ⟨t,h0,h0pos,?_⟩
  intro h hh
  obtain ⟨fit,ht⟩ := H h hh
  refine ⟨fit,?_⟩
  intro l hl hl10 z data
  dsimp only
  let a := WrappedInput.specialize t t
  have hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (lt_of_lt_of_le h0pos hh))
  let raw := candidateBits data z hd fit.2.2.2.1 hl hl10
  let input := addressedInput (InitialFormula.sourceInput a (D*h) l z hd fit.2.2.2.1 hl hl10)
  let : NeZero (2^h) := ⟨pow_ne_zero h (by omega)⟩
  obtain ⟨b,hb,HC⟩ := ht l hl10 z raw (candidate_length_le data z hd fit.2.2.2.1 hl hl10)
  have HM := input.certificate_machine_iff coding δ localCircuit (2^(h/5)) (Nat.pow_pos (by omega))
    (input_short a h D l z fit hd hl hl10) (layout h a.length D fit) rfl (output true) data
  change (∃cert : Fin (2^h)→Bool, ∀i,
    ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
      (input.initialBits coding (2^(h/5))) blankBits acceptBits i).Holds
      (Layout.assemble data cert)) ↔ (body D).eval (RawPreparedInputs.semantic a (D*h) l z raw)=1
  simp only [blankBits,acceptBits]
  rw [HM]
  change (OneTape.run δ (input.config (Layout.assemble data (fun _ => false))) (2^(h/5)-1)).cell 0=_ ↔ _
  have hcfg := source_config a data z hd fit.2.2.2.1 hl hl10
  change input.config _=_ at hcfg
  rw [hcfg,HC,TimedTape.output_injective.eq_iff,←hb]
  cases b <;> decide
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.TimedTape
noncomputable section
open Addressable
lemma initialBits_row {q : ℕ} (K : OneTape.Coding Γ Q) (content : List (InputBit q))
    (T : ℕ) (j : Fin (4*T)) (r : Fin K.bits) :
    (addressedInput content).initialBits K T j r=
      InitialFormula.row (K.encode ⟨blank,false,none⟩) (K.encode ⟨origin,true,some initialState⟩)
        (fun b => K.encode ⟨bitSymbol b,false,none⟩) (2*T) content j r := by
  let p : ℤ := (j.val:ℤ)-((2*T:ℕ):ℤ)
  have hn : p.toNat=j.val-2*T := by unfold p;omega
  have hz : p=0 ↔ j.val=2*T := by unfold p;omega
  change (addressedInput content).reading K p r=_
  unfold OneTape.Input.reading InitialFormula.row
  dsimp only [addressedInput]
  by_cases h0 : j.val=2*T
  · rw [ite_eq_left (hz.mpr h0),ite_eq_left h0]
  · rw [ite_eq_right (mt hz.mp h0),ite_eq_right h0]
    by_cases hg : 2*T<j.val ∧ j.val-(2*T+1)<content.length
    · have hp : 0<p.toNat ∧ p.toNat≤content.length := by omega
      rw [dite_eq_left hp,dite_eq_left hg]
      have hi : p.toNat-1=j.val-(2*T+1) := by omega
      simp only [hi]
      cases content[j.val-(2*T+1)] with
      | fixed b => rfl
      | input a n =>
        cases h0 : K.encode ⟨bitSymbol false,false,none⟩ r <;>
          cases h1 : K.encode ⟨bitSymbol true,false,none⟩ r <;> cases n <;>
          simp [InputBit.mapBool,InitialFormula.mapBit,h0,h1]
    · have hp : ¬(0<p.toNat ∧ p.toNat≤content.length) := by omega
      rw [dite_eq_right hp,dite_eq_right hg]
end
end SourceBurnside.TimedTape

namespace SourceBurnside.FiniteTable.Codec
lemma field_of_bits {H : ℕ} (bs : List Bool) (off : ℕ) (w : Raw H)
    (hw : ∀i : Fin (10000*H), bs.getD (off+i.val) false=w i) :
    (binaryValue bs/2^off)%2^(10000*H)=natCode w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,binaryValue_bit]
  by_cases hi : i<10000*H
  · simp only [hi,decide_true,Bool.true_and]
    rw [Nat.add_comm,hw ⟨i,hi⟩,natCode_bit w ⟨i,hi⟩]
  · simp [hi,natCode,binaryValue_bit]
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine
noncomputable section
section
open Addressable FiniteTable.Codec
variable {q H l : ℕ}
def candidateWord (data : DataAddress q→Bool) (hdq : 10000*H≤q) (hl10 : l≤10)
    (b : Bool) (i : Fin l) : Raw H :=
  fun j => data (b,⟨i.val,i.isLt.trans_le hl10⟩,⟨j.val,j.isLt.trans_le hdq⟩)
lemma candidate_bit (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (b : Bool) (i : Fin l) (hside : Z=false ∨ b=false) (j : Fin (10000*H)) :
    (candidateBits data Z hd hdq hl hl10).getD
      (((if b then l else 0)+i.val)*(10000*H)+j.val) false=
        candidateWord data hdq hl10 b i j := by
  let d := 10000*H
  have hi := i.isLt
  have hj : j.val<d := j.isLt
  have hd0 : 0<d := hd
  have offlt : ((if b then l else 0)+i.val)*d+j.val < if Z then l*d else 2*(l*d) := by
    cases b <;> cases Z <;> simp_all
    all_goals have hi := i.isLt; nlinarith
  have hm : (((if b then l else 0)+i.val)*d+j.val)%d=j.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  have hdiv : (((if b then l else 0)+i.val)*d+j.val)/d=(if b then l else 0)+i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd0,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hmod : (((if b then l else 0)+i.val)*d+j.val)/d%l=i.val := by
    rw [hdiv];cases b <;> simp [Nat.mod_eq_of_lt hi]
  have hb : decide (l*d≤((if b then l else 0)+i.val)*d+j.val)=b := by
    cases b <;> simp <;> nlinarith
  simp only [candidateBits,InitialFormula.inputData,List.getD_eq_getElem,List.length_map,List.length_ofFn,
    show ((if b then l else 0)+i.val)*(10000*H)+j.val<(if Z then l*(10000*H) else 2*(l*(10000*H))) from offlt,
    List.getElem_map,List.getElem_ofFn,InputBit.eval,Layout.assemble,dataAddress]
  change data (decide (l*d≤_),⟨_ ,_⟩,⟨_,_⟩)=_
  rw [hb]
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> apply Fin.ext
    · exact hmod
    · exact hm
lemma candidate_field (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (b : Bool) (i : Fin l) (hside : Z=false ∨ b=false) :
    (binaryValue (candidateBits data Z hd hdq hl hl10)/2^(((if b then l else 0)+i.val)*(10000*H)))%
      2^(10000*H)=natCode (candidateWord data hdq hl10 b i) :=
  field_of_bits _ _ _ (candidate_bit data Z hd hdq hl hl10 b i hside)
end

section
open Addressable FiniteTable.Codec Structured.Device Structured.Device.Formula
variable {q H l : ℕ}
lemma candidate_lengthOK (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10) :
    RawLocalBody.lengthOK.eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=1 := by
  simp only [RawLocalBody.lengthOK,and_eval,less_eval,equal_eval,eval,RawPreparedInputs.semantic,
    RawLocalBody.length,RawLocalBody.height,candidate_length]
  cases Z <;> simp [CellRepr.boolean]
lemma candidate_piece (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl2 : l≤2)
    (b : Bool) (i : Fin 2) (hi : i.val<l) (hside : Z=false ∨ b=false) :
    (RawLocalBody.piece b i).eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=
      natCode (candidateWord data hdq (by omega) b ⟨i.val,hi⟩) := by
  have hs : RawLocalBody.sideStart.eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=l := by
    interval_cases l <;> simp [RawLocalBody.sideStart,equal_eval,eval,RawPreparedInputs.semantic]
  have ho : (RawLocalBody.offset b i).eval (RawPreparedInputs.semantic a H l Z
      (candidateBits data Z hd hdq hl (by omega)))=((if b then l else 0)+i.val)*(10000*H) := by
    cases b
    · rfl
    · change (RawLocalBody.sideStart.eval (RawPreparedInputs.semantic a H l Z
        (candidateBits data Z hd hdq hl (by omega)))+i.val)*(10000*H)=(l+i.val)*(10000*H)
      rw [hs]
  change (binaryValue (candidateBits data Z hd hdq hl (by omega))/2^((RawLocalBody.offset b i).eval
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl (by omega)))))%2^(10000*H)=_
  rw [ho]
  exact candidate_field data Z hd hdq hl (by omega) b ⟨i.val,hi⟩ hside

lemma candidate_body_eq (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (D : ℕ) (fit : RawFit.Fits β g D H a.length) :
    (body D).eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval
      (fun i => (RawLocalBody.substitution i).eval
        (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))) := by
  rw [body,RawFit.body_eval]
  have hf : RawFit.Fits β g D (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10) 2)
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10) 1) := fit
  rw [ite_eq_left hf]
  simp only [RawLocalBody.checkedBody,and_eval,candidate_lengthOK,one_ne_zero,ite_false,
    RawLocalBody.body,bind_eval]
lemma sourceBody_boolean (D : ℕ) (v : Fin 7→ℕ) : (body D).eval v≤1 :=
  RawFixedPoint.body_boolean β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding v
lemma sourceBody_eq_one_iff_ne_zero (D : ℕ) (v : Fin 7→ℕ) : (body D).eval v=1 ↔ (body D).eval v≠0 := by
  have := sourceBody_boolean D v
  omega
end

section
open TimedTape Addressable LocalSyntax FiniteTable FiniteTable.Codec
open Structured.Device Structured.Device.Formula
variable {h D : ℕ}
def sourceInitial (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) : Task → Fin (4*2^(h/5)) → Fin β → InputBit (2^h) :=
  PredicateFormula.initial (layout h a.length D fit) blankBits initialBits bitEncoding a (D*h) hd fit.2.2.2.1
def sourceSchedule (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) : Schedule (2^h) :=
  (layout h a.length D fit).schedule localCircuit.circuit localCircuit.output
    (sourceInitial a fit hd) blankBits acceptBits
lemma sourceInitial_input (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (task : Task) :
    sourceInitial a fit hd task=(addressedInput (InitialFormula.sourceInput a (D*h)
      (task.arity.val+1) task.zeroTask hd fit.2.2.2.1 (by omega) (by have := task.arity.isLt;omega))).initialBits coding (2^(h/5)) := by
  funext j r
  exact (initialBits_row coding _ _ j r).symm
lemma physical_represents (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers → ℕ)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h) :
    (LocalBody.table β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).Represents
      v (sourceSchedule a fit hd) := by
  let : NeZero (2^h) := ⟨pow_ne_zero h (by omega)⟩
  apply PredicateFormula.physical_exact (layout h a.length D fit) localCircuit.circuit localCircuit.output
    blankBits initialBits acceptBits bitEncoding a hd fit.2.2.2.1
  · simp [LocalBody.time,LocalBody.height,eval,hheight]
  · simp [LocalBody.width,LocalBody.time,LocalBody.height,eval,hheight]
  · simp [LocalBody.origin,LocalBody.time,LocalBody.height,eval,hheight,layout]
  · exact hcode
  · exact hlen
  · simp [LocalBody.nextHeight,LocalBody.height,eval,hheight]
lemma local_zero_one (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=1) (hz : v 4=1) (hw : v 5=natCode w) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) true [w] []=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_zero_one (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · exact harity
  · exact hz
  · exact hw
lemma local_zero_two (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w x : Raw h)
    (hheight : v 2=h) (harity : v 3=2) (hz : v 4=1)
    (hw : v 5=natCode w) (hx : v 6=natCode x) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) true [w,x] []=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_zero_two (H:=LocalBody.height) (v:=v) hh _ (sourceSchedule a fit hd) w x hheight
  · simp [LocalBody.bound,LocalBody.height,eval,hheight]
  · exact harity
  · exact hz
  · exact hw
  · exact hx
lemma local_rep_one (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w y : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=1) (hz : v 4=0) (hw : v 5=natCode w) (hy : v 7=natCode y) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) false [w] [y]=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_rep_one (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w y hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · exact harity
  · exact hz
  · exact hw
  · exact hy
lemma local_rep_two (hh : 4≤h) (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (v : LocalBody.Registers→ℕ) (w x y z : Raw h)
    (hcode : v 0=binaryValue a) (hlen : v 1=a.length) (hheight : v 2=h)
    (harity : v 3=2) (hz : v 4=0) (hw : v 5=natCode w) (hx : v 6=natCode x)
    (hy : v 7=natCode y) (hz' : v 8=natCode z) :
    (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔
      entry (by omega) (sourceSchedule a fit hd) (10000*(D*h)) false [w,x] [y,z]=true := by
  unfold LocalBody.body
  apply PredicateFormula.normalEntry_rep_two (H:=LocalBody.height) (v:=v) hh _ (physical_represents a fit hd v hcode hlen hheight) w x y z hheight
  · simp [LocalBody.size,LocalBody.height,eval,hheight,Nat.mul_assoc]
  · simp [LocalBody.bound,LocalBody.height,eval,hheight]
  · exact harity
  · exact hz
  · exact hw
  · exact hx
  · exact hy
  · exact hz'
end

section
open Addressable FiniteTable.Codec Structured.Device Structured.Device.Formula
variable {q H l D : ℕ}
lemma candidate_entry (hH : 4≤H) (a : List Bool) (data : DataAddress q→Bool) (Z : Bool)
    (hd : 0<10000*H) (hdq : 10000*H≤q) (hl : 0<l) (hl10 : l≤10)
    (fit : RawFit.Fits β g D H a.length) (hdnext : 0<10000*(D*H)) :
    (body D).eval (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))=1 ↔
      entry (by omega) (sourceSchedule a fit hdnext) (10000*(D*H)) Z
        (List.ofFn (candidateWord data hdq hl10 false))
        (if Z then [] else List.ofFn (candidateWord data hdq hl10 true))=true := by
  rw [sourceBody_eq_one_iff_ne_zero,candidate_body_eq a data Z hd hdq hl hl10 D fit]
  let v : LocalBody.Registers→ℕ := fun i => (RawLocalBody.substitution i).eval
    (RawPreparedInputs.semantic a H l Z (candidateBits data Z hd hdq hl hl10))
  change (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v≠0 ↔ _
  by_cases h1 : l=1
  · subst l
    cases Z
    · have Hc := local_rep_one hH a fit hdnext v
        (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 true 0)
        rfl rfl rfl rfl rfl
        (candidate_piece a data false hd hdq hl (by omega) false 0 (by decide) (Or.inl rfl))
        (candidate_piece a data false hd hdq hl (by omega) true 0 (by decide) (Or.inl rfl))
      simpa only [Bool.false_eq_true,ite_false,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
    · have Hc := local_zero_one hH a fit hdnext v
        (candidateWord data hdq hl10 false 0) rfl rfl rfl rfl rfl
        (candidate_piece a data true hd hdq hl (by omega) false 0 (by decide) (Or.inr rfl))
      simpa only [ite_true,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
  · by_cases h2 : l=2
    · subst l
      cases Z
      · have Hc := local_rep_two hH a fit hdnext v
          (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 false 1)
          (candidateWord data hdq hl10 true 0) (candidateWord data hdq hl10 true 1)
          rfl rfl rfl rfl rfl
          (candidate_piece a data false hd hdq hl (by omega) false 0 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) false 1 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) true 0 (by decide) (Or.inl rfl))
          (candidate_piece a data false hd hdq hl (by omega) true 1 (by decide) (Or.inl rfl))
        simpa only [Bool.false_eq_true,ite_false,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
      · have Hc := local_zero_two hH a fit hdnext v
          (candidateWord data hdq hl10 false 0) (candidateWord data hdq hl10 false 1) rfl rfl rfl
          (candidate_piece a data true hd hdq hl (by omega) false 0 (by decide) (Or.inr rfl))
          (candidate_piece a data true hd hdq hl (by omega) false 1 (by decide) (Or.inr rfl))
        simpa only [ite_true,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one] using Hc
    · have hb : (LocalBody.body β g D localCircuit.circuit localCircuit.output blankBits initialBits acceptBits bitEncoding).eval v=0 := by
        apply PredicateFormula.normalEntry_other
        · exact h1
        · exact h2
      rw [hb]
      simp only [ne_eq,not_true_eq_false,false_iff]
      cases Z
      · simp only [entry_replacement,Bool.false_eq_true,ite_false]
        intro he
        have Hlen := FiniteTable.Codec.replacement_lengths hH _ _ _ _ he
        simp only [List.length_ofFn] at Hlen
        omega
      · simp only [ite_true,entry_zero,true_and]
        intro he
        have Hlen := FiniteTable.Codec.zero_lengths (by omega : 0<H) _ _ _ he
        simp only [List.length_ofFn] at Hlen
        omega
end

open TimedTape Addressable LocalSyntax FiniteTable FiniteTable.Codec

theorem fixed_table_certificate (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 4≤h0), ∀(h : ℕ) (hh : h0≤h),
      let a := WrappedInput.specialize t t
      ∃(fit : RawFit.Fits β g D h a.length) (fitnext : RawFit.Fits β g D (D*h) a.length),
      ∀(task : Task) (data : DataAddress (2^h)→Bool),
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
      let hdnext : 0<10000*(D*(D*h)) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      (∃cert : Fin (2^h)→Bool, ∀i,
        ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
          (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble data cert)) ↔
      entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) task.zeroTask
        (List.ofFn (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) false))
        (if task.zeroTask then [] else List.ofFn
          (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) true))=true := by
  obtain ⟨t,u,hu,H⟩ := tableau_selfpoint D hD
  refine ⟨t,max 4 u,by omega,?_⟩
  intro h hh
  have h4 : 4≤h := by omega
  have huh : u≤h := by omega
  have hnext : u≤D*h := by nlinarith
  obtain ⟨fit,ht⟩ := H h huh
  obtain ⟨fitnext,_⟩ := H (D*h) hnext
  refine ⟨fit,fitnext,?_⟩
  intro task data
  dsimp only
  let a := WrappedInput.specialize t t
  have hd : 0<10000*(D*h) := by positivity
  have hdnext : 0<10000*(D*(D*h)) := by positivity
  have hl : 0<task.arity.val+1 := by omega
  have hl10 : task.arity.val+1≤10 := by have := task.arity.isLt;omega
  have Hb := ht (task.arity.val+1) hl hl10 task.zeroTask data
  have He := candidate_entry (by nlinarith : 4≤D*h) a data task.zeroTask hd fit.2.2.2.1 hl hl10 fitnext hdnext
  rw [sourceInitial_input]
  exact Hb.trans He
end
end SourceBurnside.SourceMachine

end OAI
