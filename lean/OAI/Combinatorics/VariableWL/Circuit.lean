import OAI.Combinatorics.VariableWL.SubcubicGame

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14

namespace VariableWL.Circuit
attribute [local instance] Classical.propDecidable
open VariableWL.ScalarImages
variable (S : Type uVariable1) (A : Type uVariable2) (E : Type uVariable3)
abbrev Gate := S ⊕ A
abbrev Port := S ⊕ (A × Bool)

abbrev target : Port S A → Gate S A
  | .inl s => .inl s
  | .inr (a,_) => .inr a

abbrev Value : Gate S A → Type
  | .inl _ => Bit
  | .inr _ => Pair

def output : (g : Gate S A) → Value S A g → Bit
  | .inl _ => id
  | .inr _ => sum

def input : (p : Port S A) → Value S A (target S A p) → Bit
  | .inl _ => id
  | .inr (_,false) => Prod.fst
  | .inr (_,true) => Prod.snd

structure System where
  source : E → Gate S A
  destination : E → Port S A
  seeds : Set S
  tests : Set S
  terminal : ∀ s ∈ tests, ∀ e, source e ≠ .inl s

variable {S A E}
namespace System
variable (C : System S A E)

inductive TrueGate : Gate S A → Prop
  | seed (s : S) (hs : s ∈ C.seeds) : TrueGate (.inl s)
  | scalar (e : E) (s : S) (he : C.destination e=.inl s)
      (hs : TrueGate (C.source e)) : TrueGate (.inl s)
  | and (a : A) (e f : E) (he : C.destination e=.inr (a,false))
      (hf : C.destination f=.inr (a,true))
      (hs : TrueGate (C.source e)) (ht : TrueGate (C.source f)) : TrueGate (.inr a)

def TruePort (p : Port S A) : Prop := ∃ e, C.destination e=p ∧ C.TrueGate (C.source e)

theorem true_scalar_iff (s : S) : C.TrueGate (.inl s) ↔ s ∈ C.seeds ∨ C.TruePort (.inl s) := by
  constructor
  · intro h
    cases h with
    | seed s hs => exact Or.inl hs
    | scalar e s he hs => exact Or.inr ⟨e,he,hs⟩
  · rintro (hs | ⟨e,he,hs⟩)
    · exact .seed _ hs
    · exact .scalar e s he hs

theorem true_and_iff (a : A) : C.TrueGate (.inr a) ↔
    C.TruePort (.inr (a,false)) ∧ C.TruePort (.inr (a,true)) := by
  constructor
  · intro h
    cases h with
    | and a e f he hf hs ht => exact ⟨⟨e,he,hs⟩,⟨f,hf,ht⟩⟩
  · rintro ⟨⟨e,he,hs⟩,⟨f,hf,ht⟩⟩
    exact .and a e f he hf hs ht

structure Witness where
  gates : ∀ g : Gate S A, Set (Value S A g)
  buffers : E → Set Pair
  gates_nonempty : ∀ g, (gates g).Nonempty
  buffers_nonempty : ∀ e, (buffers e).Nonempty
  first : ∀ e, output S A (C.source e) '' gates (C.source e)=Prod.fst '' buffers e
  second : ∀ e, output S A (C.source e) '' gates (C.source e)=Prod.snd '' buffers e
  last : ∀ e, sum '' buffers e=input S A (C.destination e) '' gates (target S A (C.destination e))
  seed : ∀ s ∈ C.seeds, gates (.inl s)={0}
  test : ∀ s ∈ C.tests, gates (.inl s)={1}

namespace Witness
variable {C} (Q : C.Witness)

theorem propagates (e : E)
    (hs : output S A (C.source e) '' Q.gates (C.source e)={0}) :
    input S A (C.destination e) '' Q.gates (target S A (C.destination e))={0} :=
  zero_propagates (Q.buffers_nonempty e) ((Q.first e).symm.trans hs)
    ((Q.second e).symm.trans hs) (Q.last e)

theorem true_zero {g : Gate S A} (hg : C.TrueGate g) : output S A g '' Q.gates g={0} := by
  induction hg with
  | seed s hs => simpa [output] using Q.seed s hs
  | scalar e s he hs ih =>
    have hz := Q.propagates e ih
    have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) he
    rw [heq] at hz
    simpa [input,output] using hz
  | and a e f he hf hs ht ihe ihf =>
    have h0 : Prod.fst '' Q.gates (.inr a)={0} := by
      have hz := Q.propagates e ihe
      have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) he
      rw [heq] at hz
      exact hz
    have h1 : Prod.snd '' Q.gates (.inr a)={0} := by
      have hz := Q.propagates f ihf
      have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) hf
      rw [heq] at hz
      exact hz
    change sum '' Q.gates (.inr a)={0}
    rw [zero_buffer_unique (Q.gates_nonempty (.inr a)) h0 h1]
    simp [sum]

include Q in
theorem tests_false : ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s) := by
  intro s hs ht
  have h := Q.true_zero ht
  have he : ({1} : Set Bit)={0} := by simp [output,Q.test s hs] at h
  have hz : (1 : Bit)=0 := Set.mem_singleton_iff.mp (he ▸ Set.mem_singleton (1 : Bit))
  exact one_ne_zero hz
end Witness

variable (hfalse : ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s))

noncomputable def gateSets : (g : Gate S A) → Set (Value S A g)
  | .inl s => if s ∈ C.tests then {1} else {x | C.TrueGate (.inl s) → x=0}
  | .inr a => andWitness (C.TruePort (.inr (a,false))) (C.TruePort (.inr (a,true)))

theorem gateSets_nonempty (g : Gate S A) : (C.gateSets g).Nonempty := by
  classical
  cases g with
  | inl s =>
    by_cases hs : s ∈ C.tests
    · exact ⟨1,by simp [gateSets,hs]⟩
    · exact ⟨0,by simp [gateSets,hs]⟩
  | inr a => exact andWitness_nonempty _ _

theorem gateSets_output_scalar {s : S} (hs : s ∉ C.tests) :
    output S A (.inl s) '' C.gateSets (.inl s)={x | C.TrueGate (.inl s) → x=0} := by
  simp [output,gateSets,hs]

theorem gateSets_output_and (a : A) :
    output S A (.inr a) '' C.gateSets (.inr a)={x | C.TrueGate (.inr a) → x=0} := by
  rw [output,gateSets,andWitness_sum]
  simp only [C.true_and_iff]

theorem gateSets_source (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)={x | C.TrueGate (C.source e) → x=0} := by
  cases h : C.source e with
  | inl s => exact C.gateSets_output_scalar (fun hs => C.terminal s hs e h)
  | inr a => exact C.gateSets_output_and a

include hfalse in
theorem gateSets_input_true {p : Port S A} (hp : C.TruePort p) :
    input S A p '' C.gateSets (target S A p)={0} := by
  classical
  rcases p with s | ⟨a,b⟩
  · have ht : C.TrueGate (.inl s) := (C.true_scalar_iff s).mpr (Or.inr hp)
    have hnt : s ∉ C.tests := fun hs => hfalse s hs ht
    simp [input,target,gateSets,hnt,ht]
  · cases b
    · change Prod.fst '' andWitness _ _={0}
      rw [andWitness_fst]
      ext x
      simp [hp]
    · change Prod.snd '' andWitness _ _={0}
      rw [andWitness_snd]
      ext x
      simp [hp]

noncomputable def bufferSets (e : E) : Set Pair :=
  if C.TrueGate (C.source e) then {(0,0)}
  else buffer (input S A (C.destination e) '' C.gateSets (target S A (C.destination e)))

theorem bufferSets_nonempty (e : E) : (C.bufferSets e).Nonempty := by
  classical
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simpa only [bufferSets,ite_eq_right hs] using
      buffer_nonempty ((C.gateSets_nonempty _).image _)

theorem bufferSets_first (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)=Prod.fst '' C.bufferSets e := by
  classical
  rw [C.gateSets_source]
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simp only [bufferSets,hs,false_implies,Set.ofPred_true]
    exact (buffer_image_fst ((C.gateSets_nonempty _).image _)).symm

theorem bufferSets_second (e : E) :
    output S A (C.source e) '' C.gateSets (C.source e)=Prod.snd '' C.bufferSets e := by
  classical
  rw [C.gateSets_source]
  by_cases hs : C.TrueGate (C.source e)
  · simp [bufferSets,hs]
  · simp only [bufferSets,hs,false_implies,Set.ofPred_true]
    exact (buffer_image_snd ((C.gateSets_nonempty _).image _)).symm

include hfalse in
theorem bufferSets_last (e : E) :
    sum '' C.bufferSets e=input S A (C.destination e) '' C.gateSets (target S A (C.destination e)) := by
  classical
  by_cases hs : C.TrueGate (C.source e)
  · rw [C.gateSets_input_true hfalse ⟨e,rfl,hs⟩]
    simp [bufferSets,hs,sum]
  · simpa only [bufferSets,ite_eq_right hs] using buffer_image_sum _

noncomputable def witness : C.Witness where
  gates := C.gateSets
  buffers := C.bufferSets
  gates_nonempty := C.gateSets_nonempty
  buffers_nonempty := C.bufferSets_nonempty
  first := C.bufferSets_first
  second := C.bufferSets_second
  last := C.bufferSets_last hfalse
  seed s hs := by
    have ht : C.TrueGate (.inl s) := .seed s hs
    have hnt : s ∉ C.tests := fun he => hfalse s he ht
    simp [gateSets,hnt,ht]
  test s hs := by simp [gateSets,hs]

theorem consistent_iff : Nonempty C.Witness ↔ ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s) :=
  ⟨fun ⟨Q⟩ => Q.tests_false,fun h => ⟨C.witness h⟩⟩

end System
end VariableWL.Circuit

namespace VariableWL.Circuit
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {S : Type uVariable4} {A : Type uVariable5}

abbrev dimension : Gate S A → ℕ
  | .inl _ => 1
  | .inr _ => 2

def scalarVector (x : Bit) : Vec 1 := fun _ => x
def pairVector (x : ScalarImages.Pair) : Vec 2 := fun i => if i.val=0 then x.1 else x.2

def vector (g : Gate S A) : Value S A g → Vec (dimension g) :=
  match g with
  | .inl _ => scalarVector
  | .inr _ => pairVector

def scalarValue (x : Vec 1) : Bit := x 0
def pairValue (x : Vec 2) : ScalarImages.Pair := (x 0,x 1)

def value (g : Gate S A) : Vec (dimension g) → Value S A g :=
  match g with
  | .inl _ => scalarValue
  | .inr _ => pairValue

@[simp] theorem scalarValue_vector (x : Bit) : scalarValue (scalarVector x)=x := rfl
@[simp] theorem pairValue_vector (x : ScalarImages.Pair) : pairValue (pairVector x)=x := by
  simp [pairValue,pairVector]
@[simp] theorem scalarVector_value (x : Vec 1) : scalarVector (scalarValue x)=x := by
  funext i
  exact congrArg x (Subsingleton.elim _ _)
@[simp] theorem pairVector_value (x : Vec 2) : pairVector (pairValue x)=x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem value_vector (g : Gate S A) (x : Value S A g) : value g (vector g x)=x := by
  cases g <;> simp [value,vector]
@[simp] theorem vector_value (g : Gate S A) (x : Vec (dimension g)) : vector g (value g x)=x := by
  cases g <;> simp [value,vector]

def outputLinear (g : Gate S A) : Vec (dimension g) →ₗ[Bit] Bit :=
  match g with
  | .inl _ => LinearMap.proj 0
  | .inr _ => (LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit) + LinearMap.proj 1

def inputLinear (p : Port S A) : Vec (dimension (target S A p)) →ₗ[Bit] Bit :=
  match p with
  | .inl _ => LinearMap.proj 0
  | .inr (_,false) => LinearMap.proj 0
  | .inr (_,true) => LinearMap.proj 1

@[simp] theorem outputLinear_vector (g : Gate S A) (x : Value S A g) :
    outputLinear g (vector g x)=output S A g x := by
  cases g <;> rfl
@[simp] theorem inputLinear_vector (p : Port S A) (x : Value S A (target S A p)) :
    inputLinear p (vector (target S A p) x)=input S A p x := by
  rcases p with s | ⟨a,b⟩
  · rfl
  · cases b <;> rfl
@[simp] theorem output_value (g : Gate S A) (x : Vec (dimension g)) :
    output S A g (value g x)=outputLinear g x := by
  rw [← outputLinear_vector,vector_value]
@[simp] theorem input_value (p : Port S A) (x : Vec (dimension (target S A p))) :
    input S A p (value (target S A p) x)=inputLinear p x := by
  rw [← inputLinear_vector,vector_value]

def gateAt {X : Type uVariable6} : Gate S A → X → Gate (S × X) (A × X)
  | .inl s,x => .inl (s,x)
  | .inr a,x => .inr (a,x)

def portAt {X : Type uVariable7} : Port S A → X → Port (S × X) (A × X)
  | .inl s,x => .inl (s,x)
  | .inr (a,b),x => .inr ((a,x),b)

@[simp] theorem target_portAt {X : Type uVariable8} (p : Port S A) (x : X) :
    target (S × X) (A × X) (portAt p x)=gateAt (target S A p) x := by
  cases p <;> rfl

structure Description (r : ℕ) (S : Type uVariable9) (A : Type uVariable10) (E : Type uVariable11) (R : Type uVariable12) where
  source : E → Gate S A
  destination : E → Port S A
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  map : E → Fin r → Bool → Bool
  map_injective : ∀ e i, Set.InjOn (map e i) (domain e i)
  requestGate : R → S
  requestTest : R → Bool
  requestDomain : R → Fin r → Finset Bool
  request_nonempty : ∀ b i, (requestDomain b i).Nonempty

namespace Description
open ProductImages.Instance
variable {r : ℕ} {E : Type uVariable13} {R : Type uVariable14} (D : Description r S A E R)

def Allowed (e : E) (a : Address r) : Prop := ∀ i, a i ∈ D.domain e i
def RequestAllowed (b : R) (a : Address r) : Prop := ∀ i, a i ∈ D.requestDomain b i
def mapAddress (e : E) (a : Address r) : Address r := fun i => D.map e i (a i)

abbrev ExpandedEdges := Σ e, {a : Address r // D.Allowed e a}

def requests (v : Bool) : Set (S × Address r) :=
  {x | ∃ b, D.requestGate b=x.1 ∧ D.requestTest b=v ∧ D.RequestAllowed b x.2}

def Terminal : Prop := ∀ s a, (s,a) ∈ D.requests true →
  ∀ e z, D.Allowed e z → gateAt (D.source e) z ≠ .inl (s,a)

abbrev expanded (h : D.Terminal) : System (S × Address r) (A × Address r) D.ExpandedEdges where
  source x := gateAt (D.source x.1) x.2.val
  destination x := portAt (D.destination x.1) (D.mapAddress x.1 x.2.val)
  seeds := D.requests false
  tests := D.requests true
  terminal := fun ⟨s,a⟩ hs ⟨e,z⟩ => h s a hs e z.val z.property

abbrev Real := Gate S A ⊕ (E ⊕ Unit)
abbrev Comparison := (E ⊕ (E ⊕ E)) ⊕ R

abbrev realDimension : Real (S := S) (A := A) (E := E) → ℕ
  | .inl g => dimension g
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

abbrev comparisonSource : Comparison (E := E) (R := R) → Real (S := S) (A := A) (E := E)
  | .inl (.inl e) => .inl (D.source e)
  | .inl (.inr (.inl e)) => .inl (D.source e)
  | .inl (.inr (.inr e)) => .inr (.inl e)
  | .inr b => .inl (.inl (D.requestGate b))

abbrev comparisonTarget : Comparison (E := E) (R := R) → Real (S := S) (A := A) (E := E)
  | .inl (.inl e) => .inr (.inl e)
  | .inl (.inr (.inl e)) => .inr (.inl e)
  | .inl (.inr (.inr e)) => .inl (target S A (D.destination e))
  | .inr _ => .inr (.inr ())

abbrev consistency : ProductImages.Instance r
    (Real (S := S) (A := A) (E := E)) (Comparison (E := E) (R := R)) where
  dimension := realDimension
  dimension_one_or_two p := by
    rcases p with (s | a) | (e | u) <;> simp [realDimension,dimension]
  source := D.comparisonSource
  target := D.comparisonTarget
  domain c := match c with
    | .inl (.inl e) => D.domain e
    | .inl (.inr (.inl e)) => D.domain e
    | .inl (.inr (.inr e)) => D.domain e
    | .inr b => D.requestDomain b
  domain_nonempty c i := by
    rcases c with (e | (e | e)) | b
    · exact D.domain_nonempty e i
    · exact D.domain_nonempty e i
    · exact D.domain_nonempty e i
    · exact D.request_nonempty b i
  map c := match c with
    | .inl (.inl _) => fun _ => id
    | .inl (.inr (.inl _)) => fun _ => id
    | .inl (.inr (.inr e)) => D.map e
    | .inr _ => fun _ => id
  map_injective c i := by
    rcases c with (e | (e | e)) | b
    · exact Function.injective_id.injOn
    · exact Function.injective_id.injOn
    · exact D.map_injective e i
    · exact Function.injective_id.injOn
  linearLeft c := match c with
    | .inl (.inl e) => outputLinear (D.source e)
    | .inl (.inr (.inl e)) => outputLinear (D.source e)
    | .inl (.inr (.inr _)) => (LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit) + LinearMap.proj 1
    | .inr _ => LinearMap.proj 0
  linearRight c := match c with
    | .inl (.inl _) => LinearMap.proj 0
    | .inl (.inr (.inl _)) => LinearMap.proj 1
    | .inl (.inr (.inr e)) => inputLinear (D.destination e)
    | .inr _ => 0
  constantLeft _ := 0
  constantRight c := match c with
    | .inl _ => 0
    | .inr b => if D.requestTest b then 1 else 0

theorem real_count [Fintype S] [Fintype A] [Fintype E] :
    Fintype.card (Real (S := S) (A := A) (E := E))=
      Fintype.card S+Fintype.card A+Fintype.card E+1 := by
  simp [Real,Fintype.card_sum,Nat.add_assoc]

theorem comparison_count [Fintype E] [Fintype R] :
    Fintype.card (Comparison (E := E) (R := R))=3*Fintype.card E+Fintype.card R := by
  simp only [Comparison,Fintype.card_sum]
  omega

end Description
end VariableWL.Circuit

end OAI
