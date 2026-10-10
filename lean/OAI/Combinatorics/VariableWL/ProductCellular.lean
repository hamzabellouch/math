import OAI.Combinatorics.VariableWL.Binary

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Circuit.ProductCellular
open Binary ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m : ℕ}

abbrev Address (d : ℕ) := Fin (d+d) → Bool

def timeBits (x : Address d) : Digits d := fun i => x (i.castAdd d)
def positionBits (x : Address d) : Digits d := fun i => x (Fin.natAdd d i)
def join {α : Type uVariable2} (x y : Fin d → α) : Fin (d+d) → α := Fin.addCases x y

@[simp] theorem join_left {α : Type uVariable3} (x y : Fin d → α) (i : Fin d) : join x y (i.castAdd d)=x i :=
  Fin.addCases_left i
@[simp] theorem join_right {α : Type uVariable4} (x y : Fin d → α) (i : Fin d) : join x y (Fin.natAdd d i)=y i :=
  Fin.addCases_right i
@[simp] theorem join_addNat {α : Type uVariable5} (x y : Fin d → α) (i : Fin d) : join x y (i.addNat d)=y i := by
  rw [← Fin.natAdd_eq_addNat]
  exact join_right x y i
@[simp] theorem time_join (x y : Digits d) : timeBits (join x y)=x := by funext i; simp [timeBits]
@[simp] theorem position_join (x y : Digits d) : positionBits (join x y)=y := by funext i; simp [positionBits]
@[simp] theorem join_parts (x : Address d) : join (timeBits x) (positionBits x)=x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [timeBits,positionBits]

theorem all_parts {P : Fin (d+d) → Prop} : (∀ i, P i) ↔
    (∀ i : Fin d, P (i.castAdd d)) ∧ (∀ i : Fin d, P (Fin.natAdd d i)) := Fin.forall_fin_add P

abbrev Kind (d : ℕ) := (Fin d × Option (Fin d)) ⊕ (Fin d ⊕ ((Fin d × Option (Fin d)) ⊕ Bool))
abbrev Edge (L : Type uVariable6) (d : ℕ) := Cellular.Triple L × Kind d

def left (h : Fin d) (j : Option (Fin d)) : Kind d := .inl (h,j)
def center (h : Fin d) : Kind d := .inr (.inl h)
def right (h : Fin d) (j : Option (Fin d)) : Kind d := .inr (.inr (.inl (h,j)))
def same (v : Bool) : Kind d := .inr (.inr (.inr v))

def timeDomain : Kind d → Fin d → Finset Bool
  | .inl (h,_) => Binary.domain true h
  | .inr (.inl h) => Binary.domain true h
  | .inr (.inr (.inl (h,_))) => Binary.domain true h
  | .inr (.inr (.inr _)) => fun _ => Finset.univ

def positionDomain : Kind d → Fin d → Finset Bool
  | .inl (_,j) => cyclicDomain true j
  | .inr (.inl _) => fun _ => Finset.univ
  | .inr (.inr (.inl (_,j))) => cyclicDomain false j
  | .inr (.inr (.inr _)) => fun _ => Finset.univ

def timeMap : Kind d → Fin d → Bool → Bool
  | .inl (h,_) => table h
  | .inr (.inl h) => table h
  | .inr (.inr (.inl (h,_))) => table h
  | .inr (.inr (.inr _)) => fun _ => id

def positionMap : Kind d → Fin d → Bool → Bool
  | .inl (_,j) => cyclicTable j
  | .inr (.inl _) => fun _ => id
  | .inr (.inr (.inl (_,j))) => cyclicTable j
  | .inr (.inr (.inr _)) => fun _ => id

def source : Edge L d → Gate L (Cellular.Triple L × Bool)
  | ((a,_,_),.inl _) => .inl a
  | ((_,b,_),.inr (.inl _)) => .inl b
  | ((_,_,c),.inr (.inr (.inl _))) => .inl c
  | (abc,.inr (.inr (.inr v))) => .inr (abc,v)

def destination (rule : L → L → L → L) : Edge L d → Port L (Cellular.Triple L × Bool)
  | (abc,.inl _) => .inr ((abc,false),false)
  | (abc,.inr (.inl _)) => .inr ((abc,false),true)
  | (abc,.inr (.inr (.inl _))) => .inr ((abc,true),true)
  | (abc,.inr (.inr (.inr false))) => .inr ((abc,true),false)
  | ((a,b,c),.inr (.inr (.inr true))) => .inl (rule a b c)

theorem timeDomain_nonempty (k : Kind d) (i : Fin d) : (timeDomain k i).Nonempty := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals simp only [timeDomain]
  all_goals first | exact Binary.domain_nonempty _ _ _ | exact ⟨false,Finset.mem_univ _⟩

theorem positionDomain_nonempty (k : Kind d) (i : Fin d) : (positionDomain k i).Nonempty := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals simp only [positionDomain]
  all_goals first | exact cyclicDomain_nonempty _ _ _ | exact ⟨false,Finset.mem_univ _⟩

theorem timeMap_injective (k : Kind d) (i : Fin d) : Function.Injective (timeMap k i) := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals first | exact table_injective _ _ | exact Function.injective_id

theorem positionMap_injective (k : Kind d) (i : Fin d) : Function.Injective (positionMap k i) := by
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  all_goals first | exact cyclicTable_injective _ _ | exact Function.injective_id

structure Data (L : Type uVariable7) (d m : ℕ) where
  rule : L → L → L → L
  input : Fin m → L
  blank : L
  accepting : Set L
  fits : m < 2^d

namespace Data
variable (D : Data L d m)
noncomputable def threshold : Digits d := (Binary.equivalence d).symm ⟨m,D.fits⟩
@[simp] theorem number_threshold : number D.threshold=m := by
  have h := congrArg Fin.val ((Binary.equivalence d).apply_symm_apply ⟨m,D.fits⟩)
  exact h

abbrev Request := (Fin m ⊕ Option {h : Fin d // D.threshold h=false}) ⊕ {f : L // f ∈ D.accepting}

def requestGate : D.Request → L
  | .inl (.inl j) => D.input j
  | .inl (.inr _) => D.blank
  | .inr f => f.val

def requestTest : D.Request → Bool
  | .inl _ => false
  | .inr _ => true

noncomputable def inputBits (j : Fin m) : Digits d := (Binary.equivalence d).symm ⟨j.val,j.isLt.trans D.fits⟩
@[simp] theorem number_inputBits (j : Fin m) : number (D.inputBits j)=j.val :=
  congrArg Fin.val ((Binary.equivalence d).apply_symm_apply ⟨j.val,j.isLt.trans D.fits⟩)

noncomputable def requestTimeDomain : D.Request → Fin d → Finset Bool
  | .inl _ => fun _ => {false}
  | .inr _ => fun _ => {true}
noncomputable def requestPositionDomain : D.Request → Fin d → Finset Bool
  | .inl (.inl j) => fun i => {D.inputBits j i}
  | .inl (.inr h) => thresholdDomain D.threshold h
  | .inr _ => fun _ => Finset.univ

noncomputable def description : Description (d+d) L (Cellular.Triple L × Bool) (Edge L d) D.Request where
  source := source
  destination := destination D.rule
  domain e := join (timeDomain e.2) (positionDomain e.2)
  domain_nonempty e i := Fin.addCases (fun j => by simpa using timeDomain_nonempty e.2 j)
    (fun j => by simpa using positionDomain_nonempty e.2 j) i
  map e := join (timeMap e.2) (positionMap e.2)
  map_injective e i := by
    apply Function.Injective.injOn
    exact Fin.addCases (fun j => by simpa using timeMap_injective e.2 j)
      (fun j => by simpa using positionMap_injective e.2 j) i
  requestGate := D.requestGate
  requestTest := D.requestTest
  requestDomain b := join (D.requestTimeDomain b) (D.requestPositionDomain b)
  request_nonempty b i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rcases b with (j|h)|f <;> simp [requestTimeDomain]
    · rcases b with (j|h)|f
      · simp [requestPositionDomain]
      · simpa [requestPositionDomain] using thresholdDomain_nonempty D.threshold h _
      · simp [requestPositionDomain]

@[simp] theorem allowed_parts (abc : Cellular.Triple L) (k : Kind d) (x : Address d) :
    D.description.Allowed (abc,k) x ↔
    (∀ i, timeBits x i ∈ timeDomain k i) ∧ (∀ i, positionBits x i ∈ positionDomain k i) := by
  unfold Description.Allowed
  rw [all_parts]
  simp only [description,join_left,join_right,timeBits,positionBits]

@[simp] theorem time_mapAddress (e : Edge L d) (x : Address d) :
    timeBits (D.description.mapAddress e x)=fun i => timeMap e.2 i (timeBits x i) := by
  funext i
  simp [Description.mapAddress,description,timeBits]
@[simp] theorem position_mapAddress (e : Edge L d) (x : Address d) :
    positionBits (D.description.mapAddress e x)=fun i => positionMap e.2 i (positionBits x i) := by
  funext i
  simp [Description.mapAddress,description,positionBits]

@[simp] theorem request_parts (b : D.Request) (x : Address d) :
    D.description.RequestAllowed b x ↔
    (∀ i, timeBits x i ∈ D.requestTimeDomain b i) ∧
      (∀ i, positionBits x i ∈ D.requestPositionDomain b i) := by
  unfold Description.RequestAllowed
  rw [all_parts]
  simp only [description,join_left,join_right,timeBits,positionBits]

noncomputable def initial (j : Fin (2^d)) : L := if h : j.val < m then D.input ⟨j.val,h⟩ else D.blank

theorem seeds_exact (f : L) (x : Address d) : (f,x) ∈ D.description.requests false ↔
    number (timeBits x)=0 ∧ f=D.initial (Binary.equivalence d (positionBits x)) := by
  classical
  have ht : (∀ i, timeBits x i=false) ↔ number (timeBits x)=0 := by
    constructor
    · intro h; rw [funext h,number_false]
    · intro h
      have he := number_injective (h.trans (number_false d).symm)
      exact congrFun he
  constructor
  · rintro ⟨b,hg,hb,hreq⟩
    rcases b with (j|h)|f'
    · have hp := (D.request_parts _ _).mp hreq
      have hx : positionBits x=D.inputBits j := funext (fun i => Finset.mem_singleton.mp (hp.2 i))
      refine ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),?_⟩
      change D.input j=f at hg
      rw [initial,equivalence_val,hx,D.number_inputBits]
      simpa using hg.symm
    · have hp := (D.request_parts _ _).mp hreq
      have hj : m ≤ number (positionBits x) := by
        rw [← D.number_threshold]
        exact (threshold_exact _ _).mp ⟨h,hp.2⟩
      refine ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),?_⟩
      change D.blank=f at hg
      simp [initial,not_lt.mpr hj,hg]
    · cases hb
  · rintro ⟨hx,hf⟩
    by_cases hj : number (positionBits x) < m
    · let j : Fin m := ⟨number (positionBits x),hj⟩
      refine ⟨.inl (.inl j),?_,rfl,?_⟩
      · change D.input j=f
        simpa [initial,hj,j] using hf.symm
      · apply (D.request_parts _ _).mpr
        refine ⟨fun i => by simpa [requestTimeDomain] using (ht.mpr hx i),?_⟩
        have hp : positionBits x=D.inputBits j := number_injective (by rw [D.number_inputBits])
        intro i
        simp [requestPositionDomain,← hp]
    · obtain ⟨h,hh⟩ := (threshold_exact D.threshold (positionBits x)).mpr (by rw [D.number_threshold]; omega)
      refine ⟨.inl (.inr h),?_,rfl,?_⟩
      · change D.blank=f
        simpa [initial,hj] using hf.symm
      · exact (D.request_parts _ _).mpr
          ⟨fun i => by simpa [requestTimeDomain] using (ht.mpr hx i),hh⟩

theorem tests_exact (f : L) (x : Address d) : (f,x) ∈ D.description.requests true ↔
    number (timeBits x)=2^d-1 ∧ f ∈ D.accepting := by
  classical
  have ht : (∀ i, timeBits x i=true) ↔ number (timeBits x)=2^d-1 := by
    have hb := number_true d
    constructor
    · intro h; rw [funext h]; omega
    · intro h
      have he := number_injective (a₁ := timeBits x) (a₂ := fun _ => true) (by omega)
      exact congrFun he
  constructor
  · rintro ⟨b,hg,hb,hreq⟩
    rcases b with (j|h)|f'
    · cases hb
    · cases hb
    · have hp := (D.request_parts _ _).mp hreq
      change f'.val=f at hg
      exact ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),hg ▸ f'.property⟩
  · rintro ⟨hx,hf⟩
    refine ⟨.inr ⟨f,hf⟩,rfl,rfl,(D.request_parts _ _).mpr ⟨?_,?_⟩⟩
    · intro i; simpa [requestTimeDomain] using ht.mpr hx i
    · intro i; simp [requestPositionDomain]

theorem terminal : D.description.Terminal := by
  intro f x hx e z hz he
  obtain ⟨ht,_⟩ := (D.tests_exact f x).mp hx
  rcases e with ⟨⟨a,b,c⟩,(⟨h,j⟩|h|⟨h,j⟩|v)⟩
  all_goals try { cases he }
  all_goals
    have hxz : z=x := congrArg (fun g : Gate (L × Address d) ((Cellular.Triple L × Bool) × Address d) =>
      match g with | .inl s => s.2 | .inr s => s.2) he
    have hh := (D.allowed_parts _ _ _).mp hz |>.1
    have hi := number_flip h (timeBits z) hh
    have hb := number_lt (Binary.flip h (timeBits z))
    rw [hxz,ht] at hi
    rw [hxz] at hb
    have hpow : 0<2^d := pow_pos (by decide) _
    omega

end Data

 theorem schema_count [Fintype L] : Fintype.card (Edge L d)=Fintype.card L^3*(2*d^2+3*d+2) := by
  simp [Edge,Kind,Cellular.Triple,Fintype.card_prod,Fintype.card_sum,Fintype.card_option]
  ring

end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable8} {d m : ℕ}

instance powTwoNeZero (d : ℕ) : NeZero (2^d) := ⟨pow_ne_zero _ (by decide)⟩

noncomputable def position (x : Address d) : Fin (2^d) := Binary.equivalence d (positionBits x)

theorem address_ext {x y : Address d} (ht : number (timeBits x)=number (timeBits y))
    (hp : position x=position y) : x=y := by
  have htime := number_injective ht
  have hpos := (Binary.equivalence d).injective hp
  rw [← join_parts x,← join_parts y,htime,hpos]

@[simp] theorem position_index_join (t p : Digits d) : position (join t p)=Binary.equivalence d p := by
  simp only [position,ProductCellular.position_join]

theorem index_increment (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed true h x) :
    Binary.equivalence d (cyclicFlip h x)=Binary.equivalence d x+1 := by
  apply Fin.ext
  simpa only [equivalence_val,Fin.val_add,Fin.val_one',Nat.add_mod_mod] using cyclic_increment h x hx

theorem index_decrement (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed false h x) :
    Binary.equivalence d (cyclicFlip h x)=Binary.equivalence d x-1 := by
  by_cases hd : d=0
  · subst d
    have : Subsingleton (Fin (2^0)) := by change Subsingleton (Fin 1); infer_instance
    exact Subsingleton.elim _ _
  · have hp : 1 < 2^d := by
      obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
      have he : 0 < 2^e := pow_pos (by decide) _
      rw [pow_succ]
      omega
    apply Fin.ext
    simp only [equivalence_val,Fin.val_sub,Fin.val_one',Nat.mod_eq_of_lt hp]
    have he := cyclic_decrement h x hx
    convert he using 1
    congr 1
    omega

namespace Data
variable (D : Data L d m)

noncomputable abbrev system := D.description.expanded D.terminal

noncomputable def cellular : Cellular.Data L (Fin (2^d)) where
  rule := D.rule
  previous := fun j => j-1
  next := fun j => j+1
  initial := D.initial
  accepting := D.accepting

noncomputable abbrev state (t : ℕ) (j : Fin (2^d)) := D.cellular.state t j

 theorem left_coordinates (abc : Cellular.Triple L) (h : Fin d) (j : Option (Fin d))
    (x : Address d) (hx : D.description.Allowed (abc,left h j) x) :
    number (timeBits (D.description.mapAddress (abc,left h j) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,left h j) x)=position x+1 := by
  obtain ⟨ht,hp⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · change Binary.equivalence d (positionBits (D.description.mapAddress (abc,left h j) x))=Binary.equivalence d (positionBits x)+1
    rw [position_mapAddress]
    change Binary.equivalence d (Binary.cyclicFlip j (positionBits x))=Binary.equivalence d (positionBits x)+1
    exact index_increment j (positionBits x) hp

 theorem center_coordinates (abc : Cellular.Triple L) (h : Fin d)
    (x : Address d) (hx : D.description.Allowed (abc,center h) x) :
    number (timeBits (D.description.mapAddress (abc,center h) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,center h) x)=position x := by
  obtain ⟨ht,_⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · simp only [position,position_mapAddress,positionMap,center,id_eq]

 theorem right_coordinates (abc : Cellular.Triple L) (h : Fin d) (j : Option (Fin d))
    (x : Address d) (hx : D.description.Allowed (abc,right h j) x) :
    number (timeBits (D.description.mapAddress (abc,right h j) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,right h j) x)=position x-1 := by
  obtain ⟨ht,hp⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · change Binary.equivalence d (positionBits (D.description.mapAddress (abc,right h j) x))=Binary.equivalence d (positionBits x)-1
    rw [position_mapAddress]
    change Binary.equivalence d (Binary.cyclicFlip j (positionBits x))=Binary.equivalence d (positionBits x)-1
    exact index_decrement j (positionBits x) hp

@[simp] theorem same_allowed (abc : Cellular.Triple L) (v : Bool) (x : Address d) :
    D.description.Allowed (abc,same v) x := by
  simp [allowed_parts,timeDomain,positionDomain,same]

@[simp] theorem same_map (abc : Cellular.Triple L) (v : Bool) (x : Address d) :
    D.description.mapAddress (abc,same v) x=x := by
  apply address_ext
  · simp only [time_mapAddress,timeMap,same,id_eq]
  · simp only [position,position_mapAddress,positionMap,same,id_eq]

def gateMeaning : Gate (L × Address d) ((Cellular.Triple L × Bool) × Address d) → Prop
  | .inl (f,x) => D.state (number (timeBits x)) (position x)=f
  | .inr (((a,b,_),false),x) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=a ∧ D.state (number (timeBits x)-1) (position x)=b
  | .inr (((a,b,c),true),x) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=a ∧ D.state (number (timeBits x)-1) (position x)=b ∧
      D.state (number (timeBits x)-1) (position x+1)=c

def portMeaning : Port (L × Address d) ((Cellular.Triple L × Bool) × Address d) → Prop
  | .inl s => D.gateMeaning (.inl s)
  | .inr (((abc,false),x),false) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x-1)=abc.1
  | .inr (((abc,false),x),true) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x)=abc.2.1
  | .inr (((abc,true),x),false) => D.gateMeaning (.inr ((abc,false),x))
  | .inr (((abc,true),x),true) => 0 < number (timeBits x) ∧
      D.state (number (timeBits x)-1) (position x+1)=abc.2.2

 theorem meaningful_edge (e : D.description.ExpandedEdges) :
    D.gateMeaning (D.system.source e) → D.portMeaning (D.system.destination e) := by
  rcases e with ⟨⟨⟨a,b,c⟩,k⟩,x,hx⟩
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  · obtain ⟨ht,hp⟩ := D.left_coordinates (a,b,c) h j x hx
    change D.state (number (timeBits x)) (position x)=a →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),left h j) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),left h j) x))-1)
        (position (D.description.mapAddress ((a,b,c),left h j) x)-1)=a
    simp only [ht,hp,Nat.add_sub_cancel,add_sub_cancel_right,Nat.zero_lt_succ,true_and]
    exact id
  · obtain ⟨ht,hp⟩ := D.center_coordinates (a,b,c) h x hx
    change D.state (number (timeBits x)) (position x)=b →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),center h) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),center h) x))-1)
        (position (D.description.mapAddress ((a,b,c),center h) x))=b
    simp only [ht,hp,Nat.add_sub_cancel,Nat.zero_lt_succ,true_and]
    exact id
  · obtain ⟨ht,hp⟩ := D.right_coordinates (a,b,c) h j x hx
    change D.state (number (timeBits x)) (position x)=c →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),right h j) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),right h j) x))-1)
        (position (D.description.mapAddress ((a,b,c),right h j) x)+1)=c
    simp only [ht,hp,Nat.add_sub_cancel,sub_add_cancel,Nat.zero_lt_succ,true_and]
    exact id
  · cases v
    · change D.gateMeaning (.inr (((a,b,c),false),x)) →
        D.gateMeaning (.inr (((a,b,c),false),D.description.mapAddress ((a,b,c),same false) x))
      rw [D.same_map]
      exact id
    · change D.gateMeaning (.inr (((a,b,c),true),x)) →
        D.state (number (timeBits (D.description.mapAddress ((a,b,c),same true) x)))
          (position (D.description.mapAddress ((a,b,c),same true) x))=D.rule a b c
      rw [D.same_map]
      rintro ⟨ht,ha,hb,hc⟩
      have he : number (timeBits x)=(number (timeBits x)-1)+1 := by omega
      change D.cellular.state (number (timeBits x)) (position x)=D.rule a b c
      rw [he,Cellular.Data.state]
      change D.rule (D.state (number (timeBits x)-1) (position x-1))
        (D.state (number (timeBits x)-1) (position x))
        (D.state (number (timeBits x)-1) (position x+1))=D.rule a b c
      rw [ha,hb,hc]

 theorem true_meaning {g} (h : D.system.TrueGate g) : D.gateMeaning g := by
  induction h with
  | seed s hs =>
    rcases s with ⟨f,x⟩
    obtain ⟨ht,hf⟩ := (D.seeds_exact f x).mp hs
    change D.cellular.state (number (timeBits x)) (position x)=f
    rw [ht,Cellular.Data.state]
    exact hf.symm
  | scalar e s he hs ih =>
    have hh := D.meaningful_edge e ih
    rw [he] at hh
    exact hh
  | and a e f he hf hs ht ihe ihf =>
    have hh := D.meaningful_edge e ihe
    have hk := D.meaningful_edge f ihf
    rw [he] at hh
    rw [hf] at hk
    rcases a with ⟨⟨abc,v⟩,x⟩
    cases v
    · exact ⟨hh.1,hh.2,hk.2⟩
    · exact ⟨hh.1,hh.2.1,hh.2.2,hk.2⟩

end Data
end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable9} {d m : ℕ}

noncomputable def previousTime (x : Address d) : Digits d :=
  (Binary.equivalence d).symm ⟨number (timeBits x)-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) (number_lt _)⟩
noncomputable def backAddress (x : Address d) (j : Fin (2^d)) : Address d :=
  join (previousTime x) ((Binary.equivalence d).symm j)

@[simp] theorem number_previousTime (x : Address d) : number (previousTime x)=number (timeBits x)-1 :=
  congrArg Fin.val ((Binary.equivalence d).apply_symm_apply _)
@[simp] theorem time_backAddress (x : Address d) (j : Fin (2^d)) :
    number (timeBits (backAddress x j))=number (timeBits x)-1 := by
  simp only [backAddress,time_join,number_previousTime]
@[simp] theorem position_backAddress (x : Address d) (j : Fin (2^d)) : position (backAddress x j)=j := by
  simp only [backAddress,position_index_join,Equiv.apply_symm_apply]

theorem previousTime_case (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ h, Binary.Allowed true h (previousTime x) := by
  apply exists_allowed
  intro he
  have ht := number_lt (timeBits x)
  have ht' := number_true d
  rw [← he,number_previousTime] at ht'
  omega

namespace Data
variable (D : Data L d m)

theorem incoming_left (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.1,backAddress x (position x-1)) ∧
      D.system.destination e=.inr (((abc,false),x),false) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x-1)
  obtain ⟨j,hj⟩ := exists_cyclicAllowed true (positionBits z)
  have hz : D.description.Allowed (abc,left h j) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,left] using hh i,hj⟩
  have hm : D.description.mapAddress (abc,left h j) z=x := by
    obtain ⟨ht,hp⟩ := D.left_coordinates abc h j z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x-1)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact by simp only [z,position_backAddress,sub_add_cancel]
  refine ⟨⟨(abc,left h j),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,false),false)) (D.description.mapAddress (abc,left h j) z)=_
  rw [hm]
  rfl

theorem incoming_center (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.2.1,backAddress x (position x)) ∧
      D.system.destination e=.inr (((abc,false),x),true) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x)
  have hz : D.description.Allowed (abc,center h) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,center] using hh i,
      fun i => Finset.mem_univ _⟩
  have hm : D.description.mapAddress (abc,center h) z=x := by
    obtain ⟨ht,hp⟩ := D.center_coordinates abc h z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact position_backAddress x _
  refine ⟨⟨(abc,center h),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,false),true)) (D.description.mapAddress (abc,center h) z)=_
  rw [hm]
  rfl

theorem incoming_right (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.2.2,backAddress x (position x+1)) ∧
      D.system.destination e=.inr (((abc,true),x),true) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x+1)
  obtain ⟨j,hj⟩ := exists_cyclicAllowed false (positionBits z)
  have hz : D.description.Allowed (abc,right h j) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,right] using hh i,hj⟩
  have hm : D.description.mapAddress (abc,right h j) z=x := by
    obtain ⟨ht,hp⟩ := D.right_coordinates abc h j z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x+1)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact by simp only [z,position_backAddress,add_sub_cancel_right]
  refine ⟨⟨(abc,right h j),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,true),true)) (D.description.mapAddress (abc,right h j) z)=_
  rw [hm]
  rfl

theorem state_true (x : Address d) :
    D.system.TrueGate (.inl (D.state (number (timeBits x)) (position x),x)) := by
  have hall : ∀ t, ∀ x : Address d, number (timeBits x)=t →
      D.system.TrueGate (.inl (D.state t (position x),x)) := by
    intro t
    induction t with
    | zero =>
      intro x hx
      apply System.TrueGate.seed
      exact (D.seeds_exact _ _).mpr ⟨hx,rfl⟩
    | succ t ih =>
      intro x hx
      have hxpos : 0 < number (timeBits x) := by omega
      let abc : Cellular.Triple L := (D.state t (position x-1),D.state t (position x),D.state t (position x+1))
      obtain ⟨e0,hs0,hp0⟩ := D.incoming_left abc x hxpos
      obtain ⟨e1,hs1,hp1⟩ := D.incoming_center abc x hxpos
      obtain ⟨e2,hs2,hp2⟩ := D.incoming_right abc x hxpos
      have hi (j : Fin (2^d)) : number (timeBits (backAddress x j))=t := by rw [time_backAddress,hx]; omega
      have ht0 : D.system.TrueGate (D.system.source e0) := by
        rw [hs0]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x-1)) (hi _)
      have ht1 : D.system.TrueGate (D.system.source e1) := by
        rw [hs1]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x)) (hi _)
      have ht2 : D.system.TrueGate (D.system.source e2) := by
        rw [hs2]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x+1)) (hi _)
      have hu : D.system.TrueGate (.inr ((abc,false),x)) := .and _ e0 e1 hp0 hp1 ht0 ht1
      let e3 : D.description.ExpandedEdges := ⟨(abc,same false),x,D.same_allowed abc false x⟩
      have hp3 : D.system.destination e3=.inr (((abc,true),x),false) := by
        change portAt (.inr ((abc,true),false)) (D.description.mapAddress (abc,same false) x)=_
        rw [D.same_map]
        rfl
      have hv : D.system.TrueGate (.inr ((abc,true),x)) := .and _ e3 e2 hp3 hp2 hu ht2
      let e4 : D.description.ExpandedEdges := ⟨(abc,same true),x,D.same_allowed abc true x⟩
      apply System.TrueGate.scalar e4 _ _ hv
      change portAt (.inl (D.rule abc.1 abc.2.1 abc.2.2)) (D.description.mapAddress (abc,same true) x)=_
      rw [D.same_map]
      rfl
  exact hall _ x rfl

theorem scalar_true_iff (f : L) (x : Address d) : D.system.TrueGate (.inl (f,x)) ↔
    D.state (number (timeBits x)) (position x)=f := by
  refine ⟨D.true_meaning,fun h => ?_⟩
  rw [← h]
  exact D.state_true x

theorem true_test_iff : (∃ s ∈ D.system.tests, D.system.TrueGate (.inl s)) ↔
    ∃ j, D.state (2^d-1) j ∈ D.accepting := by
  constructor
  · rintro ⟨⟨f,x⟩,hs,ht⟩
    obtain ⟨hx,hf⟩ := (D.tests_exact f x).mp hs
    have he := (D.scalar_true_iff f x).mp ht
    rw [hx] at he
    exact ⟨position x,he ▸ hf⟩
  · rintro ⟨j,hj⟩
    let x : Address d := join (fun _ => true) ((Binary.equivalence d).symm j)
    have ht : number (timeBits x)=2^d-1 := by
      simp only [x,time_join]
      have h := number_true d
      omega
    have hp : position x=j := by simp only [x,position_index_join,Equiv.apply_symm_apply]
    refine ⟨(D.state (2^d-1) j,x),(D.tests_exact _ _).mpr ⟨ht,hj⟩,?_⟩
    apply (D.scalar_true_iff _ _).mpr
    rw [ht,hp]

theorem consistency_iff : D.description.consistency.Consistent ↔
    ∀ j, D.state (2^d-1) j ∉ D.accepting := by
  rw [D.description.consistency_iff D.terminal]
  simpa only [not_exists,not_and] using not_congr D.true_test_iff

end Data
end VariableWL.Circuit.ProductCellular

end OAI
