import OAI.Computability.WeisfeilerLeman.Enumeration

namespace OAI

universe uA uB uG uE uAlphabet uJ

namespace WLTime.CircuitEncoding
abbrev Bit := ZMod 2

def zeroSet {d : ℕ} (f : Fin d → Prop) : Set (Fin d → Bit) :=
  {x | ∀ i, f i → x i = 0}

theorem zeroSet_nonempty {d : ℕ} (f : Fin d → Prop) : (zeroSet f).Nonempty :=
  ⟨0,fun _ _ => rfl⟩

theorem image_singleton_of_forall {A : Type uA} {B : Type uB} {S : Set A} (hS : S.Nonempty)
    (f : A → B) (b : B) (h : ∀ x ∈ S, f x=b) : f '' S = {b} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · rintro _ rfl
    obtain ⟨x,hx⟩ := hS
    exact ⟨x,hx,h x hx⟩

theorem const_image {A : Type uA} {B : Type uB} {S : Set A} (hS : S.Nonempty) (b : B) :
    (fun _ : A => b) '' S = {b} :=
  image_singleton_of_forall hS _ _ (fun _ _ => rfl)

theorem value_of_image_singleton {A : Type uA} {B : Type uB} {S : Set A} {f : A → B} {b : B}
    (h : f '' S = {b}) {x : A} (hx : x ∈ S) : f x=b := by
  have hm := Set.mem_image_of_mem f hx
  rw [h] at hm
  exact hm

open scoped Classical in
theorem zeroSet_coord_image {d : ℕ} (f : Fin d → Prop) (i : Fin d) :
    (fun x : Fin d → Bit => x i) '' zeroSet f = if f i then {0} else Set.univ := by
  by_cases hi : f i
  · rw [ite_eq_left hi]
    exact image_singleton_of_forall (zeroSet_nonempty f) _ _ (fun _ hx => hx i hi)
  · rw [ite_eq_right hi]
    apply Set.eq_univ_of_forall
    intro b
    refine ⟨Function.update (fun _ => 0) i b,?_,Function.update_self _ _ _⟩
    intro j hj
    apply Function.update_of_ne
    intro h
    exact hi (h ▸ hj)

open scoped Classical in
theorem zeroSet_sum_image {d : ℕ} (f : Fin d → Prop) :
    (fun x : Fin d → Bit => ∑ i,x i) '' zeroSet f =
      if ∀ i,f i then {0} else Set.univ := by
  by_cases hf : ∀ i,f i
  · rw [ite_eq_left hf]
    apply image_singleton_of_forall (zeroSet_nonempty f)
    intro x hx
    simp only [hx _ (hf _),Finset.sum_const_zero]
  · rw [ite_eq_right hf]
    push Not at hf
    obtain ⟨i,hi⟩ := hf
    apply Set.eq_univ_of_forall
    intro b
    refine ⟨Function.update (fun _ => 0) i b,?_,?_⟩
    · intro j hj
      apply Function.update_of_ne
      intro h
      exact hi (h ▸ hj)
    · simp [Finset.sum_update_of_mem]

def diode (D : Set Bit) : Set (Fin 2 → Bit) := {z | z 0 + z 1 ∈ D}

theorem diode_nonempty {D : Set Bit} (hD : D.Nonempty) : (diode D).Nonempty := by
  obtain ⟨d,hd⟩ := hD
  exact ⟨![0,d],by simpa [diode] using hd⟩

theorem diode_coord_image {D : Set Bit} (hD : D.Nonempty) (i : Fin 2) :
    (fun z : Fin 2 → Bit => z i) '' diode D = Set.univ := by
  obtain ⟨d,hd⟩ := hD
  apply Set.eq_univ_of_forall
  intro a
  fin_cases i
  · refine ⟨![a,d-a],?_,by simp⟩
    simpa [diode,add_sub_cancel_left] using hd
  · refine ⟨![d-a,a],?_,by simp⟩
    simpa [diode] using hd

theorem diode_sum_image {D : Set Bit} :
    (fun z : Fin 2 → Bit => z 0+z 1) '' diode D = D := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩; exact hz
  · intro a ha
    exact ⟨![0,a],by simpa [diode] using ha,by simp⟩

inductive Kind where
  | scalar | both
  deriving DecidableEq

def Kind.dim : Kind → ℕ
  | .scalar => 1
  | .both => 2

theorem Kind.dim_pos (k : Kind) : 0 < k.dim := by cases k <;> decide

structure Circuit (G : Type uG) (E : Type uE) where
  kind : G → Kind
  src : E → G
  dst : E → G
  port : (e : E) → Fin (kind (dst e)).dim
  rank : G → ℕ
  forward : ∀ e, rank (src e) < rank (dst e)
  seed : G → Bool
  test : G → Bool
  seed_scalar : ∀ g, seed g = true → kind g = .scalar
  test_scalar : ∀ g, test g = true → kind g = .scalar
  test_terminal : ∀ e, test (src e) = false

namespace Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

def TrueAt (g : G) : Prop :=
  if C.kind g = .scalar then C.seed g = true ∨ ∃ (e : E) (_h : C.dst e=g), TrueAt (C.src e)
  else ∀ p : Fin (C.kind g).dim,
    ∃ (e : E) (_h : C.dst e=g), (C.port e).val = p.val ∧ TrueAt (C.src e)
termination_by C.rank g
decreasing_by
  all_goals
    subst g
    exact C.forward _

def PortTrue (g : G) (p : ℕ) : Prop :=
  ∃ e, C.dst e=g ∧ (C.port e).val=p ∧ C.TrueAt (C.src e)

def Forced (g : G) (i : Fin (C.kind g).dim) : Prop :=
  if C.kind g = .scalar then C.TrueAt g else C.PortTrue g i.val

abbrev Value (g : G) := Fin (C.kind g).dim → Bit

def output (g : G) (x : C.Value g) : Bit := ∑ i,x i

structure Witness where
  gate : (g : G) → Set (C.Value g)
  buffer : E → Set (Fin 2 → Bit)
  gate_nonempty : ∀ g, (gate g).Nonempty
  buffer_nonempty : ∀ e, (buffer e).Nonempty
  first : ∀ e, C.output (C.src e) '' gate (C.src e) = (fun z => z 0) '' buffer e
  second : ∀ e, C.output (C.src e) '' gate (C.src e) = (fun z => z 1) '' buffer e
  third : ∀ e, (fun z => z 0+z 1) '' buffer e = (fun x => x (C.port e)) '' gate (C.dst e)
  seeds : ∀ g, C.seed g = true → C.output g '' gate g = {0}
  tests : ∀ g, C.test g = true → C.output g '' gate g = {1}

end Circuit
end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

theorem all_forced_iff (g : G) : (∀ i,C.Forced g i) ↔ C.TrueAt g := by
  by_cases hs : C.kind g = .scalar
  · simp only [Forced,ite_eq_left hs]
    exact ⟨fun h => h ⟨0,(C.kind g).dim_pos⟩,fun h _ => h⟩
  · rw [TrueAt]
    simp only [hs,ite_false,Forced,PortTrue,exists_prop]

theorem port_true_forced (g : G) (p : Fin (C.kind g).dim)
    (h : C.PortTrue g p.val) : C.Forced g p := by
  by_cases hs : C.kind g = .scalar
  · simp only [Forced,ite_eq_left hs]
    rw [TrueAt,ite_eq_left hs]
    obtain ⟨e,he,_,ht⟩ := h
    exact Or.inr ⟨e,he,ht⟩
  · simpa only [Forced,ite_eq_right hs] using h

theorem true_of_seed (g : G) (h : C.seed g = true) : C.TrueAt g := by
  rw [TrueAt,ite_eq_left (C.seed_scalar g h)]
  exact Or.inl h

theorem output_scalar_eq_port (g : G) (hs : C.kind g = .scalar)
    (p : Fin (C.kind g).dim) (x : C.Value g) : C.output g x = x p := by
  classical
  apply Finset.sum_eq_single p
  · intro i _ hip
    exfalso
    apply hip
    apply Fin.ext
    have hi := i.isLt
    have hp := p.isLt
    simp only [hs,Kind.dim] at hi hp
    omega
  · simp

namespace Witness
variable {C} (W : C.Witness)

theorem port_zero (e : E) (h : C.output (C.src e) '' W.gate (C.src e) = {0}) :
    (fun x => x (C.port e)) '' W.gate (C.dst e) = {0} := by
  rw [← W.third e]
  apply image_singleton_of_forall (W.buffer_nonempty e)
  intro z hz
  rw [value_of_image_singleton ((W.first e).symm.trans h) hz,
    value_of_image_singleton ((W.second e).symm.trans h) hz,zero_add]

theorem output_zero (g : G)
    (h : ∀ p : Fin (C.kind g).dim, (fun x => x p) '' W.gate g = {0}) :
    C.output g '' W.gate g = {0} := by
  apply image_singleton_of_forall (W.gate_nonempty g)
  intro x hx
  unfold output
  apply Finset.sum_eq_zero
  intro i _
  exact value_of_image_singleton (h i) hx

theorem true_output_zero (g : G) (ht : C.TrueAt g) : C.output g '' W.gate g = {0} := by
  induction g using (measure C.rank).wf.induction with
  | h g ih =>
    rw [TrueAt] at ht
    split_ifs at ht with hs
    · rcases ht with hseed | ⟨e,he,hsrc⟩
      · exact W.seeds g hseed
      · subst g
        have ho := ih (C.src e) (C.forward e) hsrc
        have hp := W.port_zero e ho
        have hf : C.output (C.dst e) = fun x => x (C.port e) :=
          funext (C.output_scalar_eq_port (C.dst e) hs (C.port e))
        rw [hf]
        exact hp
    · apply W.output_zero g
      intro p
      obtain ⟨e,he,hp,hsrc⟩ := ht p
      subst g
      have ho := W.port_zero e (ih (C.src e) (C.forward e) hsrc)
      have hpp : C.port e = p := Fin.ext hp
      simpa only [hpp] using ho

include W in
theorem all_tests_false : ∀ g, C.test g = true → ¬C.TrueAt g := by
  intro g hg ht
  have he := (W.true_output_zero g ht).symm.trans (W.tests g hg)
  have : (0 : Bit)=1 := Set.singleton_injective he
  exact zero_ne_one this

end Witness

open scoped Classical in
noncomputable def canonicalGate (g : G) : Set (C.Value g) :=
  if C.test g = true then {fun _ => 1} else zeroSet (C.Forced g)

theorem canonicalGate_nonempty (g : G) : (C.canonicalGate g).Nonempty := by
  classical
  unfold canonicalGate
  split_ifs
  · exact Set.singleton_nonempty _
  · exact zeroSet_nonempty _

open scoped Classical in
theorem canonicalGate_output (g : G) :
    C.output g '' C.canonicalGate g =
      if C.test g = true then {1} else if C.TrueAt g then {0} else Set.univ := by
  by_cases ht : C.test g = true
  · rw [canonicalGate,ite_eq_left ht,ite_eq_left ht,Set.image_singleton]
    congr 1
    exact C.output_scalar_eq_port g (C.test_scalar g ht) ⟨0,(C.kind g).dim_pos⟩ _
  · rw [canonicalGate,ite_eq_right ht,ite_eq_right ht]
    exact (zeroSet_sum_image (C.Forced g)).trans (by simp only [C.all_forced_iff])

theorem canonicalGate_port_true
    (hT : ∀ g, C.test g = true → ¬C.TrueAt g) (g : G) (p : Fin (C.kind g).dim)
    (hp : C.PortTrue g p.val) :
    (fun x => x p) '' C.canonicalGate g = {0} := by
  classical
  have hf := C.port_true_forced g p hp
  have ht : C.test g ≠ true := by
    intro ht
    have hs := C.test_scalar g ht
    simp only [Forced,ite_eq_left hs] at hf
    exact hT g ht hf
  rw [canonicalGate,ite_eq_right ht,zeroSet_coord_image,ite_eq_left hf]

open scoped Classical in
noncomputable def canonicalBuffer (e : E) : Set (Fin 2 → Bit) :=
  if C.TrueAt (C.src e) then {0}
  else diode ((fun x => x (C.port e)) '' C.canonicalGate (C.dst e))

theorem canonicalBuffer_nonempty (e : E) : (C.canonicalBuffer e).Nonempty := by
  classical
  unfold canonicalBuffer
  split_ifs
  · exact Set.singleton_nonempty _
  · exact diode_nonempty ((C.canonicalGate_nonempty _).image _)

theorem canonicalBuffer_coord (e : E) (i : Fin 2) :
    (fun z => z i) '' C.canonicalBuffer e = C.output (C.src e) '' C.canonicalGate (C.src e) := by
  classical
  rw [C.canonicalGate_output,C.test_terminal]
  simp only [Bool.false_eq_true,ite_false]
  by_cases ht : C.TrueAt (C.src e)
  · simp [canonicalBuffer,ht]
  · rw [canonicalBuffer,ite_eq_right ht,ite_eq_right ht]
    exact diode_coord_image ((C.canonicalGate_nonempty _).image _) i

theorem canonicalBuffer_sum (hT : ∀ g, C.test g = true → ¬C.TrueAt g) (e : E) :
    (fun z => z 0+z 1) '' C.canonicalBuffer e =
      (fun x => x (C.port e)) '' C.canonicalGate (C.dst e) := by
  classical
  by_cases ht : C.TrueAt (C.src e)
  · rw [canonicalBuffer,ite_eq_left ht]
    rw [C.canonicalGate_port_true hT _ _ ⟨e,rfl,rfl,ht⟩]
    simp
  · rw [canonicalBuffer,ite_eq_right ht,diode_sum_image]

noncomputable def canonicalWitness (hT : ∀ g, C.test g = true → ¬C.TrueAt g) : C.Witness where
  gate := C.canonicalGate
  buffer := C.canonicalBuffer
  gate_nonempty := C.canonicalGate_nonempty
  buffer_nonempty := C.canonicalBuffer_nonempty
  first e := (C.canonicalBuffer_coord e 0).symm
  second e := (C.canonicalBuffer_coord e 1).symm
  third := C.canonicalBuffer_sum hT
  seeds := by
    intro g hg
    rw [C.canonicalGate_output]
    have htrue := C.true_of_seed g hg
    have htest : C.test g ≠ true := fun h => hT g h htrue
    rw [ite_eq_right htest,ite_eq_left htrue]
  tests := by intro g hg; rw [C.canonicalGate_output,ite_eq_left hg]

theorem witness_iff_tests_false : Nonempty C.Witness ↔ ∀ g, C.test g = true → ¬C.TrueAt g :=
  ⟨fun ⟨W⟩ => W.all_tests_false,fun h => ⟨C.canonicalWitness h⟩⟩

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

theorem truth_iff_of_equations (V : G → Prop)
    (hV : ∀ g, V g ↔ if C.kind g = .scalar then C.seed g = true ∨
      ∃ (e : E) (_h : C.dst e=g), V (C.src e)
      else ∀ p : Fin (C.kind g).dim,
        ∃ (e : E) (_h : C.dst e=g), (C.port e).val = p.val ∧ V (C.src e))
    (g : G) : C.TrueAt g ↔ V g := by
  induction g using (measure C.rank).wf.induction with
  | h g ih =>
    rw [TrueAt,hV g]
    split_ifs
    · apply or_congr Iff.rfl
      apply exists_congr
      intro e
      apply exists_congr
      intro he
      apply ih
      subst g
      exact C.forward e
    · apply forall_congr'
      intro p
      apply exists_congr
      intro e
      apply exists_congr
      intro he
      apply and_congr Iff.rfl
      apply ih
      subst g
      exact C.forward e

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.Tableau
variable {Alphabet : Type uAlphabet} {J : Type uJ} (F : Alphabet → Alphabet → Alphabet → Alphabet) (shift : Equiv.Perm J) (initial : J → Alphabet)

def update (x : J → Alphabet) : J → Alphabet := fun j => F (x (shift.symm j)) (x j) (x (shift j))
def run : ℕ → J → Alphabet
  | 0 => initial
  | t+1 => update F shift (run t)

@[simp] theorem run_zero : run F shift initial 0 = initial := rfl
@[simp] theorem run_succ (t : ℕ) (j : J) : run F shift initial (t+1) j =
    F (run F shift initial t (shift.symm j)) (run F shift initial t j)
      (run F shift initial t (shift j)) := rfl

inductive Gate (Alphabet : Type uAlphabet) where
  | scalar (f : Alphabet)
  | first (a b c : Alphabet)
  | second (a b c : Alphabet)
  deriving DecidableEq, Fintype

abbrev Node (Alphabet : Type uAlphabet) (J : Type uJ) (H : ℕ) := Gate Alphabet × Fin H × J

def Gate.kind : Gate Alphabet → Kind
  | .scalar _ => .scalar
  | _ => .both

def Gate.phase : Gate Alphabet → ℕ
  | .scalar _ => 2
  | .first _ _ _ => 0
  | .second _ _ _ => 1

def prevTime {H : ℕ} (t : Fin H) (ht : 0<t.val) : Fin H := ⟨t.val-1,by omega⟩

inductive Connection (Alphabet : Type uAlphabet) (J : Type uJ) (H : ℕ) where
  | left (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | center (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | bridge (a b c : Alphabet) (t : Fin H) (j : J)
  | right (a b c : Alphabet) (t : Fin H) (ht : 0<t.val) (j : J)
  | out (a b c : Alphabet) (t : Fin H) (j : J)

variable {H : ℕ}

def source : Connection Alphabet J H → Node Alphabet J H
  | .left a _ _ t ht j => (.scalar a,prevTime t ht,shift.symm j)
  | .center _ b _ t ht j => (.scalar b,prevTime t ht,j)
  | .bridge a b c t j => (.first a b c,t,j)
  | .right _ _ c t ht j => (.scalar c,prevTime t ht,shift j)
  | .out a b c t j => (.second a b c,t,j)

def target : Connection Alphabet J H → Node Alphabet J H
  | .left a b c t _ j => (.first a b c,t,j)
  | .center a b c t _ j => (.first a b c,t,j)
  | .bridge a b c t j => (.second a b c,t,j)
  | .right a b c t _ j => (.second a b c,t,j)
  | .out a b c t j => (.scalar (F a b c),t,j)

def port : (e : Connection Alphabet J H) → Fin (target F e).1.kind.dim
  | .left _ _ _ _ _ _ => (0 : Fin 2)
  | .center _ _ _ _ _ _ => (1 : Fin 2)
  | .bridge _ _ _ _ _ => (0 : Fin 2)
  | .right _ _ _ _ _ _ => (1 : Fin 2)
  | .out _ _ _ _ _ => (0 : Fin 1)

def rank (g : Node Alphabet J H) : ℕ := 3*g.2.1.val+g.1.phase

theorem forward (e : Connection Alphabet J H) : rank (source shift e) < rank (target F e) := by
  cases e <;> simp only [source,target,rank,Gate.phase,prevTime] <;> omega

open scoped Classical in
noncomputable def seed (g : Node Alphabet J H) : Bool := match g.1 with
  | .scalar f => decide (g.2.1.val=0 ∧ f=initial g.2.2)
  | _ => false

open scoped Classical in
noncomputable def test (accepting : Alphabet → Prop) (g : Node Alphabet J H) : Bool := match g.1 with
  | .scalar f => decide (g.2.1.val+1=H ∧ accepting f)
  | _ => false

open scoped Classical in
noncomputable def circuit (accepting : Alphabet → Prop) : Circuit (Node Alphabet J H) (Connection Alphabet J H) where
  kind g := g.1.kind
  src := source shift
  dst := target F
  port := port F
  rank := rank
  forward := forward F shift
  seed := seed initial
  test := test accepting
  seed_scalar := by rintro ⟨g,t,j⟩; cases g <;> simp [seed,Gate.kind]
  test_scalar := by rintro ⟨g,t,j⟩; cases g <;> simp [test,Gate.kind]
  test_terminal := by
    intro e
    cases e <;> simp [source,test,prevTime]
    all_goals
      apply decide_eq_false
      rintro ⟨he,_⟩
      omega

def expected (g : Node Alphabet J H) : Prop := match g.1 with
  | .scalar f => f=run F shift initial g.2.1.val g.2.2
  | .first a b _ => 0<g.2.1.val ∧
      a=run F shift initial (g.2.1.val-1) (shift.symm g.2.2) ∧
      b=run F shift initial (g.2.1.val-1) g.2.2
  | .second a b c => 0<g.2.1.val ∧
      a=run F shift initial (g.2.1.val-1) (shift.symm g.2.2) ∧
      b=run F shift initial (g.2.1.val-1) g.2.2 ∧
      c=run F shift initial (g.2.1.val-1) (shift g.2.2)

theorem incoming_first (V : Node Alphabet J H → Prop) (a b c : Alphabet) (t : Fin H) (j : J) (p : Fin 2) :
    (∃ e : Connection Alphabet J H, target F e = (.first a b c,t,j) ∧
      (port F e).val=p.val ∧ V (source shift e)) ↔
    ∃ ht : 0<t.val,
      (p=0 ∧ V (.scalar a,prevTime t ht,shift.symm j)) ∨
      (p=1 ∧ V (.scalar b,prevTime t ht,j)) := by
  constructor
  · rintro ⟨e,he,hp,hv⟩
    cases e with
    | left a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.first.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact ⟨ht',Or.inl ⟨Fin.ext hp.symm,hv⟩⟩
    | center a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.first.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact ⟨ht',Or.inr ⟨Fin.ext hp.symm,hv⟩⟩
    | bridge => simp [target] at he
    | right => simp [target] at he
    | out => simp [target] at he
  · rintro ⟨ht,⟨rfl,hv⟩ | ⟨rfl,hv⟩⟩
    · exact ⟨.left a b c t ht j,rfl,rfl,hv⟩
    · exact ⟨.center a b c t ht j,rfl,rfl,hv⟩

theorem incoming_second (V : Node Alphabet J H → Prop) (a b c : Alphabet) (t : Fin H) (j : J) (p : Fin 2) :
    (∃ e : Connection Alphabet J H, target F e = (.second a b c,t,j) ∧
      (port F e).val=p.val ∧ V (source shift e)) ↔
    (p=0 ∧ V (.first a b c,t,j)) ∨
      ∃ ht : 0<t.val, p=1 ∧ V (.scalar c,prevTime t ht,shift j) := by
  constructor
  · rintro ⟨e,he,hp,hv⟩
    cases e with
    | bridge a' b' c' t' j' =>
      simp only [target,Prod.mk.injEq,Gate.second.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact Or.inl ⟨Fin.ext hp.symm,hv⟩
    | right a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.second.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact Or.inr ⟨ht',Fin.ext hp.symm,hv⟩
    | left => simp [target] at he
    | center => simp [target] at he
    | out => simp [target] at he
  · rintro (⟨rfl,hv⟩ | ⟨ht,rfl,hv⟩)
    · exact ⟨.bridge a b c t j,rfl,rfl,hv⟩
    · exact ⟨.right a b c t ht j,rfl,rfl,hv⟩

theorem incoming_scalar (V : Node Alphabet J H → Prop) (f : Alphabet) (t : Fin H) (j : J) :
    (∃ e : Connection Alphabet J H, target F e = (.scalar f,t,j) ∧ V (source shift e)) ↔
    ∃ a b c, F a b c=f ∧ V (.second a b c,t,j) := by
  constructor
  · rintro ⟨e,he,hv⟩
    cases e with
    | out a b c t' j' =>
      simp only [target,Prod.mk.injEq,Gate.scalar.injEq] at he
      obtain ⟨hf,rfl,rfl⟩ := he
      exact ⟨a,b,c,hf,hv⟩
    | left => simp [target] at he
    | center => simp [target] at he
    | bridge => simp [target] at he
    | right => simp [target] at he
  · rintro ⟨a,b,c,hf,hv⟩
    exact ⟨.out a b c t j,by simp only [target,hf],hv⟩

theorem expected_equations (accepting : Alphabet → Prop) (g : Node Alphabet J H) :
    expected F shift initial g ↔
      if (circuit F shift initial accepting).kind g = .scalar then
        (circuit F shift initial accepting).seed g = true ∨
          ∃ (e : Connection Alphabet J H) (_h : (circuit F shift initial accepting).dst e=g),
            expected F shift initial ((circuit F shift initial accepting).src e)
      else ∀ p : Fin ((circuit F shift initial accepting).kind g).dim,
        ∃ (e : Connection Alphabet J H) (_h : (circuit F shift initial accepting).dst e=g),
          ((circuit F shift initial accepting).port e).val=p.val ∧
            expected F shift initial ((circuit F shift initial accepting).src e) := by
  classical
  rcases g with ⟨g,t,j⟩
  cases g with
  | scalar f =>
    simp only [circuit,Gate.kind,↓reduceIte,exists_prop]
    change (f=run F shift initial t.val j) ↔
      seed initial (.scalar f,t,j) = true ∨
        ∃ e : Connection Alphabet J H, target F e = (.scalar f,t,j) ∧
          expected F shift initial (source shift e)
    rw [incoming_scalar]
    simp only [seed,decide_eq_true_eq,expected]
    constructor
    · intro hf
      by_cases ht : t.val=0
      · exact Or.inl ⟨ht,by simpa only [ht,run_zero] using hf⟩
      · have hp : 0<t.val := Nat.pos_of_ne_zero ht
        have he : t.val-1+1=t.val := Nat.sub_add_cancel hp
        right
        refine ⟨run F shift initial (t.val-1) (shift.symm j),
          run F shift initial (t.val-1) j,run F shift initial (t.val-1) (shift j),?_,hp,rfl,rfl,rfl⟩
        rw [← run_succ F shift initial (t.val-1) j,he]
        exact hf.symm
    · rintro (⟨ht,hf⟩ | ⟨a,b,c,hf,ht,ha,hb,hc⟩)
      · simpa only [ht,run_zero] using hf
      · have he : t.val-1+1=t.val := Nat.sub_add_cancel ht
        rw [ha,hb,hc,← run_succ F shift initial (t.val-1) j,he] at hf
        exact hf.symm
  | first a b c =>
    simp only [circuit,Gate.kind,reduceCtorEq,↓reduceIte,exists_prop]
    change expected F shift initial (.first a b c,t,j) ↔
      ∀ p : Fin 2, ∃ e : Connection Alphabet J H, target F e=(.first a b c,t,j) ∧
        (port F e).val=p.val ∧ expected F shift initial (source shift e)
    simp_rw [incoming_first]
    simp only [Fin.forall_fin_two,expected,prevTime]
    simp
    tauto
  | second a b c =>
    simp only [circuit,Gate.kind,reduceCtorEq,↓reduceIte,exists_prop]
    change expected F shift initial (.second a b c,t,j) ↔
      ∀ p : Fin 2, ∃ e : Connection Alphabet J H, target F e=(.second a b c,t,j) ∧
        (port F e).val=p.val ∧ expected F shift initial (source shift e)
    simp_rw [incoming_second]
    simp only [Fin.forall_fin_two,expected,prevTime]
    simp
    tauto

theorem truth_iff_expected (accepting : Alphabet → Prop) (g : Node Alphabet J H) :
    (circuit F shift initial accepting).TrueAt g ↔ expected F shift initial g :=
  (circuit F shift initial accepting).truth_iff_of_equations
    (expected F shift initial) (expected_equations F shift initial accepting) g

theorem tests_false_iff (hH : 0<H) (accepting : Alphabet → Prop) :
    (∀ g : Node Alphabet J H, (circuit F shift initial accepting).test g = true →
      ¬(circuit F shift initial accepting).TrueAt g) ↔
    ∀ j, ¬accepting (run F shift initial (H-1) j) := by
  classical
  constructor
  · intro h j ha
    have ht : H-1<H := by omega
    apply h (.scalar (run F shift initial (H-1) j),⟨H-1,ht⟩,j)
    · change decide (H-1+1=H ∧ accepting (run F shift initial (H-1) j)) = true
      exact decide_eq_true ⟨by omega,ha⟩
    · exact (truth_iff_expected F shift initial accepting _).mpr rfl
  · rintro h ⟨g,t,j⟩ hg ht
    have he := (truth_iff_expected F shift initial accepting _).mp ht
    cases g with
    | scalar f =>
      change decide (t.val+1=H ∧ accepting f) = true at hg
      obtain ⟨ht,hf⟩ := of_decide_eq_true hg
      have hv : t.val=H-1 := by omega
      change f=run F shift initial t.val j at he
      exact h j (by simpa only [he,hv] using hf)
    | first => exact Bool.false_ne_true hg
    | second => exact Bool.false_ne_true hg

end WLTime.CircuitEncoding.Tableau

end OAI
