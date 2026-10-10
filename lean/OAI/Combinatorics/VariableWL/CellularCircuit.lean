import OAI.Combinatorics.VariableWL.Circuit

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Circuit
open VariableWL.Affine ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {S : Type uVariable1} {A : Type uVariable2} {r : ℕ}

noncomputable def decodeGates (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g))) :
    ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g)
  | .inl (s,a) => scalarValue '' Q (.inl s) a
  | .inr (b,a) => pairValue '' Q (.inr b) a

theorem decodeGates_nonempty (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (h : ∀ g a, (Q g a).Nonempty) (g : Gate (S × Address r) (A × Address r)) :
    (decodeGates Q g).Nonempty := by
  rcases g with ⟨s,a⟩ | ⟨b,a⟩
  · exact (h (.inl s) a).image scalarValue
  · exact (h (.inr b) a).image pairValue

theorem output_decode (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (g : Gate S A) (a : Address r) :
    output (S × Address r) (A × Address r) (gateAt g a) '' decodeGates Q (gateAt g a)=
      outputLinear g '' Q g a := by
  cases g <;> simp only [gateAt,decodeGates,Set.image_image] <;> rfl

theorem input_decode (Q : ∀ g : Gate S A, Address r → Set (Vec (dimension g)))
    (p : Port S A) (a : Address r) :
    input (S × Address r) (A × Address r) (portAt p a) ''
      decodeGates Q (target _ _ (portAt p a))=inputLinear p '' Q (target _ _ p) a := by
  rcases p with s | ⟨b,v⟩
  · simp only [portAt,target,decodeGates,Set.image_image]
    rfl
  · cases v <;> simp only [portAt,target,decodeGates,Set.image_image] <;> rfl

noncomputable def encodeGates
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g)) :
    ∀ g : Gate S A, Address r → Set (Vec (dimension g))
  | .inl s,a => scalarVector '' Q (.inl (s,a))
  | .inr b,a => pairVector '' Q (.inr (b,a))

theorem encodeGates_nonempty
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (h : ∀ g, (Q g).Nonempty) (g : Gate S A) (a : Address r) : (encodeGates Q g a).Nonempty := by
  cases g with
  | inl s => exact (h (.inl (s,a))).image scalarVector
  | inr b => exact (h (.inr (b,a))).image pairVector

theorem output_encode
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (g : Gate S A) (a : Address r) :
    outputLinear g '' encodeGates Q g a=
      output (S × Address r) (A × Address r) (gateAt g a) '' Q (gateAt g a) := by
  cases g <;> simp only [encodeGates,Set.image_image] <;> rfl

theorem input_encode
    (Q : ∀ g : Gate (S × Address r) (A × Address r), Set (Value (S × Address r) (A × Address r) g))
    (p : Port S A) (a : Address r) :
    inputLinear p '' encodeGates Q (target _ _ p) a=
      input (S × Address r) (A × Address r) (portAt p a) '' Q (target _ _ (portAt p a)) := by
  rcases p with s | ⟨b,v⟩
  · simp only [inputLinear,target,encodeGates,Set.image_image]
    rfl
  · cases v <;> simp only [inputLinear,target,encodeGates,Set.image_image] <;> rfl

theorem const_image {X : Type uVariable3} {Y : Type uVariable4} (Q : Set X) (hq : Q.Nonempty) (y : Y) :
    (fun _ : X => y) '' Q={y} := by
  ext z
  simp only [Set.mem_image,Set.mem_singleton_iff]
  exact ⟨fun ⟨_,_,he⟩ => he.symm,fun he => by subst z; obtain ⟨x,hx⟩ := hq; exact ⟨x,hx,rfl⟩⟩

namespace Description
variable {E : Type uVariable5} {R : Type uVariable6} (D : Description r S A E R)

noncomputable def decodeWitness (h : D.Terminal) (Q : D.consistency.Witness) :
    (D.expanded h).Witness where
  gates := decodeGates (fun g a => Q.values (.inl g) a)
  buffers x := pairValue '' Q.values (.inr (.inl x.1)) x.2.val
  gates_nonempty := decodeGates_nonempty _ (fun g a => Q.nonempty (.inl g) a)
  buffers_nonempty x := (Q.nonempty (.inr (.inl x.1)) x.2.val).image _
  first x := by
    change output _ _ (gateAt (D.source x.1) x.2.val) '' _ = _
    rw [output_decode]
    have hz := Q.images (.inl (.inl x.1)) x.2.val x.2.property
    change (fun v => outputLinear (D.source x.1) v+0) '' Q.values (.inl (D.source x.1)) x.2.val=
      (fun v : Vec 2 => v 0+0) '' Q.values (.inr (.inl x.1)) x.2.val at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue] using hz
  second x := by
    change output _ _ (gateAt (D.source x.1) x.2.val) '' _ = _
    rw [output_decode]
    have hz := Q.images (.inl (.inr (.inl x.1))) x.2.val x.2.property
    change (fun v => outputLinear (D.source x.1) v+0) '' Q.values (.inl (D.source x.1)) x.2.val=
      (fun v : Vec 2 => v 1+0) '' Q.values (.inr (.inl x.1)) x.2.val at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue] using hz
  last x := by
    change ScalarImages.sum '' _=input _ _ (portAt (D.destination x.1) (D.mapAddress x.1 x.2.val)) '' _
    rw [input_decode]
    have hz := Q.images (.inl (.inr (.inr x.1))) x.2.val x.2.property
    change (fun v : Vec 2 => (v 0+v 1)+0) '' Q.values (.inr (.inl x.1)) x.2.val=
      (fun v => inputLinear (D.destination x.1) v+0) ''
        Q.values (.inl (target _ _ (D.destination x.1))) (D.mapAddress x.1 x.2.val) at hz
    simpa only [add_zero,Set.image_image,Function.comp_def,pairValue,ScalarImages.sum] using hz
  seed s hs := by
    obtain ⟨b,hb,hv,ha⟩ := hs
    have hz := Q.images (.inr b) s.2 ha
    change (fun v : Vec 1 => v 0+0) '' Q.values (.inl (.inl (D.requestGate b))) s.2=
      (fun _ : Vec 1 => (0 : Bit)+(if D.requestTest b then (1 : Bit) else 0)) '' Q.values (.inr (.inr ())) s.2 at hz
    simp only [add_zero,hv,Bool.false_eq_true,ite_false] at hz
    have hc := const_image (Q.values (.inr (.inr ())) s.2) (Q.nonempty _ _) (0 : Bit)
    have heq := congrArg (fun t : S => scalarValue '' Q.values (.inl (.inl t)) s.2) hb
    exact heq.symm.trans (hz.trans hc)
  test s hs := by
    obtain ⟨b,hb,hv,ha⟩ := hs
    have hz := Q.images (.inr b) s.2 ha
    change (fun v : Vec 1 => v 0+0) '' Q.values (.inl (.inl (D.requestGate b))) s.2=
      (fun _ : Vec 1 => (0 : Bit)+(if D.requestTest b then (1 : Bit) else 0)) '' Q.values (.inr (.inr ())) s.2 at hz
    simp only [add_zero,zero_add,hv,ite_true] at hz
    have hc := const_image (Q.values (.inr (.inr ())) s.2) (Q.nonempty _ _) (1 : Bit)
    have heq := congrArg (fun t : S => scalarValue '' Q.values (.inl (.inl t)) s.2) hb
    exact heq.symm.trans (hz.trans hc)

noncomputable def encodedValues (h : D.Terminal) (Q : (D.expanded h).Witness) :
    ∀ p : (Real (S := S) (A := A) (E := E)), Address r → Set (Vec (realDimension p))
  | .inl g,a => encodeGates Q.gates g a
  | .inr (.inl e),a => if ha : D.Allowed e a then pairVector '' Q.buffers ⟨e,⟨a,ha⟩⟩ else Set.univ
  | .inr (.inr _),_ => Set.univ

theorem encodedValues_nonempty (h : D.Terminal) (Q : (D.expanded h).Witness)
    (p : (Real (S := S) (A := A) (E := E))) (a : Address r) : (D.encodedValues h Q p a).Nonempty := by
  rcases p with g | (e | u)
  · exact encodeGates_nonempty Q.gates Q.gates_nonempty g a
  · dsimp only [encodedValues]
    split_ifs with ha
    · exact (Q.buffers_nonempty _).image _
    · exact Set.univ_nonempty
  · exact Set.univ_nonempty

noncomputable def encodeWitness (h : D.Terminal) (Q : (D.expanded h).Witness) :
    D.consistency.Witness where
  values := D.encodedValues h Q
  nonempty := D.encodedValues_nonempty h Q
  images c a ha := by
    rcases c with (e | (e | e)) | b
    · change (fun v => outputLinear (D.source e) v+0) '' encodeGates Q.gates (D.source e) a=
        (fun v : Vec 2 => v 0+0) '' D.encodedValues h Q (.inr (.inl e)) a
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,output_encode,Set.image_image]
      exact Q.first ⟨e,⟨a,hea⟩⟩
    · change (fun v => outputLinear (D.source e) v+0) '' encodeGates Q.gates (D.source e) a=
        (fun v : Vec 2 => v 1+0) '' D.encodedValues h Q (.inr (.inl e)) a
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,output_encode,Set.image_image]
      exact Q.second ⟨e,⟨a,hea⟩⟩
    · change (fun v : Vec 2 => (v 0+v 1)+0) '' D.encodedValues h Q (.inr (.inl e)) a=
        (fun v => inputLinear (D.destination e) v+0) '' encodeGates Q.gates (target _ _ (D.destination e)) (D.mapAddress e a)
      simp only [add_zero]
      have hea : D.Allowed e a := ha
      rw [encodedValues,dite_eq_left hea,input_encode,Set.image_image]
      exact Q.last ⟨e,⟨a,hea⟩⟩
    · have hea : D.RequestAllowed b a := ha
      change (fun v : Vec 1 => v 0+0) '' (scalarVector '' Q.gates (.inl (D.requestGate b,a)))=
        (fun _ : Vec 1 => 0+(if D.requestTest b then (1 : Bit) else 0)) '' Set.univ
      simp only [add_zero,zero_add]
      rw [const_image _ Set.univ_nonempty,Set.image_image]
      change id '' Q.gates (.inl (D.requestGate b,a))={if D.requestTest b then (1 : Bit) else 0}
      rw [Set.image_id]
      cases hv : D.requestTest b
      · simpa only [hv,Bool.false_eq_true,ite_false] using
          Q.seed (D.requestGate b,a) ⟨b,rfl,hv,hea⟩
      · simpa only [hv,ite_true] using Q.test (D.requestGate b,a) ⟨b,rfl,hv,hea⟩

theorem consistency_iff (h : D.Terminal) : D.consistency.Consistent ↔
    ∀ s ∈ (D.expanded h).tests, ¬ (D.expanded h).TrueGate (.inl s) := by
  rw [← System.consistent_iff]
  exact ⟨fun ⟨Q⟩ => ⟨D.decodeWitness h Q⟩,fun ⟨Q⟩ => ⟨D.encodeWitness h Q⟩⟩

end Description
end VariableWL.Circuit

namespace VariableWL.Circuit.Cellular
attribute [local instance] Classical.propDecidable
variable (L : Type uVariable7) (J : Type uVariable8) (N : ℕ)
abbrev Triple := L × L × L
abbrev Scalar := L × (Fin (N+1) × J)
abbrev And := (Triple L × Bool) × (Fin (N+1) × J)
abbrev Edge := (Fin N × J × Triple L × Fin 3) ⊕ (Fin (N+1) × J × Triple L × Bool)
variable {L J N}

structure Data (L : Type uVariable9) (J : Type uVariable10) where
  rule : L → L → L → L
  previous : J → J
  next : J → J
  initial : J → L
  accepting : Set L

namespace Data
variable (D : Data L J)

def state : ℕ → J → L
  | 0 => D.initial
  | t+1 => fun j => D.rule (state t (D.previous j)) (state t j) (state t (D.next j))

def source : Edge L J N → Gate (Scalar L J N) (And L J N)
  | .inl (t,j,(a,b,c),i) => .inl (if i=0 then (a,t.castSucc,D.previous j)
      else if i=1 then (b,t.castSucc,j) else (c,t.castSucc,D.next j))
  | .inr (t,j,abc,v) => .inr ((abc,v),(t,j))

def destination : Edge L J N → Port (Scalar L J N) (And L J N)
  | .inl (t,j,abc,i) => if i=0 then .inr (((abc,false),(t.succ,j)),false)
      else if i=1 then .inr (((abc,false),(t.succ,j)),true)
      else .inr (((abc,true),(t.succ,j)),true)
  | .inr (t,j,(a,b,c),false) => .inr ((((a,b,c),true),(t,j)),false)
  | .inr (t,j,(a,b,c),true) => .inl (D.rule a b c,t,j)

abbrev system (N : ℕ) : System (Scalar L J N) (And L J N) (Edge L J N) where
  source := D.source
  destination := D.destination
  seeds := {s | s.2.1.val=0 ∧ s.1=D.initial s.2.2}
  tests := {s | s.2.1.val=N ∧ s.1 ∈ D.accepting}
  terminal s hs e := by
    rcases s with ⟨f,t,j⟩
    rcases e with ⟨u,k,⟨a,b,c⟩,i⟩ | ⟨u,k,abc,v⟩
    · dsimp only [source]
      split_ifs <;> intro he
      all_goals
        have hh := congrArg (fun g : Gate (Scalar L J N) (And L J N) =>
          match g with | .inl v => v.2.1.val | .inr _ => 0) he
        dsimp at hh
        have ht : t.val=N := hs.1
        have hu := u.isLt
        omega
    · intro he
      cases he

def gateMeaning : Gate (Scalar L J N) (And L J N) → Prop
  | .inl (f,t,j) => D.state t.val j=f
  | .inr (((a,b,_c),false),t,j) => 0<t.val ∧
      D.state (t.val-1) (D.previous j)=a ∧ D.state (t.val-1) j=b
  | .inr (((a,b,c),true),t,j) => 0<t.val ∧
      D.state (t.val-1) (D.previous j)=a ∧ D.state (t.val-1) j=b ∧
        D.state (t.val-1) (D.next j)=c

def portMeaning : Port (Scalar L J N) (And L J N) → Prop
  | .inl s => D.gateMeaning (.inl s)
  | .inr (((abc,false),(t,j)),false) => 0<t.val ∧ D.state (t.val-1) (D.previous j)=abc.1
  | .inr (((abc,false),(t,j)),true) => 0<t.val ∧ D.state (t.val-1) j=abc.2.1
  | .inr (((abc,true),(t,j)),false) => D.gateMeaning (.inr ((abc,false),(t,j)))
  | .inr (((abc,true),(t,j)),true) => 0<t.val ∧ D.state (t.val-1) (D.next j)=abc.2.2

theorem meaningful_edge (e : Edge L J N) : D.gateMeaning (D.source e) → D.portMeaning (D.destination e) := by
  rcases e with ⟨t,j,⟨a,b,c⟩,i⟩ | ⟨t,j,⟨a,b,c⟩,v⟩
  · fin_cases i <;> simp [source,destination,gateMeaning,portMeaning]
  · cases v
    · exact id
    · intro h
      obtain ⟨ht,ha,hb,hc⟩ := h
      have he : t.val=(t.val-1)+1 := by omega
      change D.state t.val j=D.rule a b c
      rw [he,state]
      simp only [ha,hb,hc]

theorem true_meaning {g : Gate (Scalar L J N) (And L J N)}
    (h : (D.system N).TrueGate g) : D.gateMeaning g := by
  induction h with
  | seed s hs =>
    rcases s with ⟨f,t,j⟩
    change D.state t.val j=f
    rw [hs.1,state]
    exact hs.2.symm
  | scalar e s he hs ih =>
    have hh := D.meaningful_edge e ih
    have hz := congrArg D.portMeaning he
    rw [hz] at hh
    exact hh
  | and a e f he hf hs ht ihe ihf =>
    have hh := D.meaningful_edge e ihe
    have hk := D.meaningful_edge f ihf
    rw [congrArg D.portMeaning he] at hh
    rw [congrArg D.portMeaning hf] at hk
    rcases a with ⟨⟨abc,v⟩,t,j⟩
    cases v
    · exact ⟨hh.1,hh.2,hk.2⟩
    · exact ⟨hh.1,hh.2.1,hh.2.2,hk.2⟩

theorem state_true (t : Fin (N+1)) (j : J) :
    (D.system N).TrueGate (.inl (D.state t.val j,t,j)) := by
  have hall : ∀ u : ℕ, ∀ hu : u<N+1, ∀ j : J,
      (D.system N).TrueGate (.inl (D.state u j,(⟨u,hu⟩ : Fin (N+1)),j)) := by
    intro u
    induction u with
    | zero =>
      intro hu j
      exact .seed _ ⟨rfl,rfl⟩
    | succ u ih =>
      intro hu j
      have hlt : u<N := by omega
      have hlt' : u<N+1 := by omega
      let t : Fin N := ⟨u,hlt⟩
      let abc : Triple L := (D.state u (D.previous j),D.state u j,D.state u (D.next j))
      let e0 : Edge L J N := .inl (t,j,abc,0)
      let e1 : Edge L J N := .inl (t,j,abc,1)
      let e2 : Edge L J N := .inl (t,j,abc,2)
      have hu' : (D.system N).TrueGate (.inr ((abc,false),(t.succ,j))) :=
        .and _ e0 e1 rfl rfl (ih hlt' (D.previous j)) (ih hlt' j)
      let e3 : Edge L J N := .inr (t.succ,j,abc,false)
      have hv' : (D.system N).TrueGate (.inr ((abc,true),(t.succ,j))) :=
        .and _ e3 e2 rfl rfl hu' (ih hlt' (D.next j))
      let e4 : Edge L J N := .inr (t.succ,j,abc,true)
      exact .scalar e4 _ rfl hv'
  exact hall t.val t.isLt j

theorem scalar_true_iff (f : L) (t : Fin (N+1)) (j : J) :
    (D.system N).TrueGate (.inl (f,t,j)) ↔ D.state t.val j=f := by
  refine ⟨D.true_meaning,fun h => ?_⟩
  rw [← h]
  exact D.state_true t j

def rank : Gate (Scalar L J N) (And L J N) → ℕ
  | .inl (_,t,_) => 3*t.val+2
  | .inr ((_,false),t,_) => 3*t.val
  | .inr ((_,true),t,_) => 3*t.val+1

theorem rank_increases (e : Edge L J N) :
    rank (D.source e)<rank (target _ _ (D.destination e)) := by
  rcases e with ⟨t,j,⟨a,b,c⟩,i⟩ | ⟨t,j,⟨a,b,c⟩,v⟩
  · fin_cases i <;> simp [source,destination,rank] <;> omega
  · cases v <;> simp [source,destination,rank]

theorem true_test_iff : (∃ s ∈ (D.system N).tests, (D.system N).TrueGate (.inl s)) ↔
    ∃ j, D.state N j ∈ D.accepting := by
  constructor
  · rintro ⟨⟨f,t,j⟩,⟨ht,hf⟩,hh⟩
    have he := D.true_meaning hh
    change D.state t.val j=f at he
    rw [ht] at he
    exact ⟨j,he ▸ hf⟩
  · rintro ⟨j,hj⟩
    exact ⟨(D.state N j,Fin.last N,j),⟨rfl,hj⟩,D.state_true (Fin.last N) j⟩

end Data
end VariableWL.Circuit.Cellular

end OAI
