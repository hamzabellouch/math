import OAI.GroupTheory.UniversalGroup.StackMachines

namespace OAI

universe u v w x

namespace Higman.AffineStack

section
open MarkerMachine
abbrev Counter := Multiplicative ℤ

def scale (b : ℤ) : Counter →* Counter where
  toFun h := Multiplicative.ofAdd (b * h.toAdd)
  map_one' := by change Multiplicative.ofAdd (b*0) = Multiplicative.ofAdd 0; simp
  map_mul' x y := by
    change Multiplicative.ofAdd (b*(x.toAdd+y.toAdd)) = Multiplicative.ofAdd (b*x.toAdd+b*y.toAdd)
    rw [mul_add]

lemma scale_injective (b : ℤ) (hb : b ≠ 0) : Function.Injective (scale b) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  exact mul_left_cancel₀ hb (congrArg Multiplicative.toAdd h)

inductive Op (Γ : Type)
  | push (a : Γ) | pop (a : Γ) | peek (a : Γ) | empty | idle

variable {Γ G Q : Type} [Group G]

def Op.Rel : Op Γ → List Γ → List Γ → Prop
  | .push a, s, t => t = a :: s
  | .pop a, s, t => s = a :: t
  | .peek a, s, t => s = t ∧ ∃ r, s = a :: r
  | .empty, s, t => s = [] ∧ t = []
  | .idle, s, t => s = t

def localEdge (b : ℤ) (digit : Γ → ℤ) (hb : b ≠ 0) (p q : Q) (w : G) :
    Op Γ → Edge G Counter Q
  | .push a => ⟨Counter, MonoidHom.id _, scale b, Function.injective_id,
      scale_injective b hb, 1, Multiplicative.ofAdd (digit a),p,q,w⟩
  | .pop a => ⟨Counter, scale b, MonoidHom.id _, scale_injective b hb,
      Function.injective_id, Multiplicative.ofAdd (digit a),1,p,q,w⟩
  | .peek a => ⟨Counter, scale b, scale b, scale_injective b hb,
      scale_injective b hb, Multiplicative.ofAdd (digit a),Multiplicative.ofAdd (digit a),p,q,w⟩
  | .empty => ⟨PUnit,1,1,Function.injective_of_subsingleton _,Function.injective_of_subsingleton _,
      Multiplicative.ofAdd 1,Multiplicative.ofAdd 1,p,q,w⟩
  | .idle => ⟨Counter, MonoidHom.id _,MonoidHom.id _,Function.injective_id,
      Function.injective_id,1,1,p,q,w⟩

instance localEdge_finitelyPresented (b : ℤ) (digit : Γ → ℤ) (hb : b ≠ 0) (p q : Q) (w : G)
    (o : Op Γ) : Group.IsFinitelyPresented (localEdge b digit hb p q w o).Domain := by
  cases o with
  | empty => exact inferInstanceAs (Group.IsFinitelyPresented PUnit)
  | push a | pop a | peek a | idle => exact inferInstanceAs (Group.IsFinitelyPresented Counter)

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

def encode (s : List Γ) : Counter := Multiplicative.ofAdd (IntegerStack.code b digit s)

include hb hd hi in
lemma encode_injective : Function.Injective (encode b digit) :=
  fun _ _ h ↦ IntegerStack.code_injective b digit hb hd hi (congrArg Multiplicative.toAdd h)

include hb hd hi in

theorem local_sound (p q : Q) (w : G) (o : Op Γ)
    (x : (localEdge b digit (by omega) p q w o).Domain) (s : List Γ)
    (h : (localEdge b digit (by omega) p q w o).inputLinear x *
      (localEdge b digit (by omega) p q w o).inputOffset = encode b digit s) :
    ∃ t, (localEdge b digit (by omega) p q w o).outputLinear x *
      (localEdge b digit (by omega) p q w o).outputOffset = encode b digit t ∧ o.Rel s t := by
  cases o with
  | push a =>
    change x * 1 = encode b digit s at h
    simp only [mul_one] at h
    subst x
    exact ⟨a::s,rfl,rfl⟩
  | pop a =>
    change Counter at x
    have hh : b*x.toAdd + digit a = IntegerStack.code b digit s :=
      congrArg Multiplicative.toAdd h
    obtain ⟨t,rfl,ht⟩ := (IntegerStack.decode_push b digit hb hd hi a x.toAdd s).mp hh
    refine ⟨t,?_,rfl⟩
    change x * 1 = encode b digit t
    rw [mul_one]
    exact Multiplicative.toAdd.injective ht
  | peek a =>
    change Counter at x
    have hh : b*x.toAdd + digit a = IntegerStack.code b digit s :=
      congrArg Multiplicative.toAdd h
    obtain ⟨t,ht,_⟩ := (IntegerStack.decode_push b digit hb hd hi a x.toAdd s).mp hh
    exact ⟨s,h,rfl,t,ht⟩
  | empty =>
    have hh : encode b digit [] = encode b digit s := by
      change (1 : Counter) * encode b digit [] = encode b digit s at h
      simpa only [one_mul] using h
    have hs : s = [] := (encode_injective b digit hb hd hi hh).symm
    exact ⟨[],rfl,hs,rfl⟩
  | idle => exact ⟨s,h,rfl⟩

include hb in

theorem local_complete (p q : Q) (w : G) (o : Op Γ) (s t : List Γ) (h : o.Rel s t) :
    ∃ x : (localEdge b digit (by omega) p q w o).Domain,
      (localEdge b digit (by omega) p q w o).inputLinear x *
        (localEdge b digit (by omega) p q w o).inputOffset = encode b digit s ∧
      (localEdge b digit (by omega) p q w o).outputLinear x *
        (localEdge b digit (by omega) p q w o).outputOffset = encode b digit t := by
  cases o with
  | push a => exact ⟨encode b digit s, mul_one _, by cases h; rfl⟩
  | pop a => exact ⟨encode b digit t, by cases h; rfl, mul_one _⟩
  | peek a =>
    obtain ⟨rfl,r,rfl⟩ := h
    exact ⟨encode b digit r,rfl,rfl⟩
  | empty =>
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨PUnit.unit,rfl,rfl⟩
  | idle => exact ⟨encode b digit s,mul_one _,by cases h; exact mul_one _⟩

end

section
open MarkerMachine
variable {K Γ G Q : Type} [DecidableEq K] [Group G]

abbrev Stores (K : Type) := K → Counter
abbrev Rest (k : K) := {j : K // j ≠ k} → Counter

def insertLinear {A : Type} [Group A] (k : K) (f : A →* Counter) :
    A × Rest k →* Stores K where
  toFun x j := if h : j = k then f x.1 else x.2 ⟨j,h⟩
  map_one' := by ext j; dsimp; split_ifs <;> simp
  map_mul' x y := by ext j; dsimp; split_ifs <;> simp

@[simp] lemma insertLinear_apply {A : Type} [Group A] (k : K) (f : A →* Counter)
    (x : A × Rest k) (j : K) : insertLinear k f x j =
      if h : j = k then f x.1 else x.2 ⟨j,h⟩ := rfl

lemma insertLinear_injective {A : Type} [Group A] (k : K) (f : A →* Counter)
    (hf : Function.Injective f) : Function.Injective (insertLinear k f) := by
  intro x y h
  apply Prod.ext
  · apply hf
    simpa [insertLinear] using congrFun h k
  · funext j
    simpa [insertLinear,j.property] using congrFun h j.val

def insertOffset (k : K) (a : Counter) : Stores K := fun j ↦ if j = k then a else 1

def liftEdge (k : K) (e : Edge G Counter Q) : Edge G (Stores K) Q where
  Domain := e.Domain × Rest k
  inputLinear := insertLinear k e.inputLinear
  outputLinear := insertLinear k e.outputLinear
  input_injective := insertLinear_injective k e.inputLinear e.input_injective
  output_injective := insertLinear_injective k e.outputLinear e.output_injective
  inputOffset := insertOffset k e.inputOffset
  outputOffset := insertOffset k e.outputOffset
  inputState := e.inputState
  outputState := e.outputState
  weight := e.weight

lemma liftEdge_finitelyPresented [Finite K] (k : K) (e : Edge G Counter Q)
    [Group.IsFinitelyPresented e.Domain] : Group.IsFinitelyPresented (liftEdge k e).Domain := by
  have : Group.IsFinitelyPresented (Rest k) := finitelyPresented_pi _ _
  exact finitelyPresented_prod

inductive Action (K Γ : Type)
  | onStack (k : K) (o : Op Γ) | idle

def Action.Rel : Action K Γ → (K → List Γ) → (K → List Γ) → Prop
  | .onStack k o, S, T => ∃ t, o.Rel (S k) t ∧ T = Function.update S k t
  | .idle, S, T => T = S

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

def encodeStores (S : K → List Γ) : Stores K := fun k ↦ encode b digit (S k)

def actionEdge (p q : Q) (w : G) : Action K Γ → Edge G (Stores K) Q
  | .onStack k o => liftEdge k (localEdge b digit (by omega) p q w o)
  | .idle => ⟨Stores K,MonoidHom.id _,MonoidHom.id _,Function.injective_id,
      Function.injective_id,1,1,p,q,w⟩

lemma action_finitelyPresented [Finite K] (p q : Q) (w : G) (a : Action K Γ) :
    Group.IsFinitelyPresented (actionEdge b digit hb p q w a).Domain := by
  cases a with
  | onStack k o => exact liftEdge_finitelyPresented _ _
  | idle => exact finitelyPresented_pi _ _

include hd hi in
theorem action_sound (p q : Q) (w : G) (a : Action K Γ)
    (x : (actionEdge b digit hb p q w a).Domain) (S : K → List Γ)
    (h : (actionEdge b digit hb p q w a).inputLinear x *
      (actionEdge b digit hb p q w a).inputOffset = encodeStores b digit S) :
    ∃ T, (actionEdge b digit hb p q w a).outputLinear x *
      (actionEdge b digit hb p q w a).outputOffset = encodeStores b digit T ∧ a.Rel S T := by
  cases a with
  | onStack k o =>
    change (localEdge b digit (by omega) p q w o).Domain × Rest k at x
    have input_eq (j : K) :
        (if hj : j = k then (localEdge b digit (by omega) p q w o).inputLinear x.1
          else x.2 ⟨j,hj⟩) *
        (if j = k then (localEdge b digit (by omega) p q w o).inputOffset else 1) =
          encode b digit (S j) := congrFun h j
    have hk : (localEdge b digit (by omega) p q w o).inputLinear x.1 *
        (localEdge b digit (by omega) p q w o).inputOffset = encode b digit (S k) := by
      simpa using input_eq k
    obtain ⟨t,ht,hr⟩ := local_sound b digit hb hd hi p q w o x.1 (S k) hk
    refine ⟨Function.update S k t,?_,t,hr,rfl⟩
    funext j
    change (if hj : j = k then (localEdge b digit (by omega) p q w o).outputLinear x.1
        else x.2 ⟨j,hj⟩) *
      (if j = k then (localEdge b digit (by omega) p q w o).outputOffset else 1) =
        encode b digit (Function.update S k t j)
    by_cases hj : j = k
    · subst j
      simpa using ht
    · simpa [hj] using input_eq j
  | idle => exact ⟨S,h,rfl⟩

theorem action_complete (p q : Q) (w : G) (a : Action K Γ) (S T : K → List Γ) (h : a.Rel S T) :
    ∃ x : (actionEdge b digit hb p q w a).Domain,
      (actionEdge b digit hb p q w a).inputLinear x *
        (actionEdge b digit hb p q w a).inputOffset = encodeStores b digit S ∧
      (actionEdge b digit hb p q w a).outputLinear x *
        (actionEdge b digit hb p q w a).outputOffset = encodeStores b digit T := by
  cases a with
  | onStack k o =>
    obtain ⟨t,hr,rfl⟩ := h
    obtain ⟨x,hs,ht⟩ := local_complete b digit hb p q w o (S k) t hr
    refine ⟨(x,fun j ↦ encode b digit (S j.val)),?_,?_⟩
    · funext j
      change (if j = k then (localEdge b digit (by omega) p q w o).inputLinear x
          else encode b digit (S j)) *
        (if j = k then (localEdge b digit (by omega) p q w o).inputOffset else 1) =
          encode b digit (S j)
      by_cases hj : j = k
      · subst j
        simpa using hs
      · simp [hj]
    · funext j
      change (if j = k then (localEdge b digit (by omega) p q w o).outputLinear x
          else encode b digit (S j)) *
        (if j = k then (localEdge b digit (by omega) p q w o).outputOffset else 1) =
          encode b digit (Function.update S k t j)
      by_cases hj : j = k
      · subst j
        simpa using ht
      · simp [hj]
  | idle => exact ⟨encodeStores b digit S,mul_one _,by cases h; exact mul_one _⟩

end

open MarkerMachine
variable {K Γ G Q : Type} [DecidableEq K] [Group G]
  (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)

@[simp] lemma actionEdge_inputState (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).inputState = p := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

@[simp] lemma actionEdge_outputState (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).outputState = q := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

@[simp] lemma actionEdge_weight (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).weight = w := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

variable (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

include hb hd hi in
omit [DecidableEq K] in
lemma encodeStores_injective : Function.Injective (encodeStores (K := K) b digit) := by
  intro S T h
  funext k
  exact encode_injective b digit hb hd hi (congrFun h k)

end Higman.AffineStack

namespace Higman.StackProgram

section
open AffineStack MarkerMachine
variable {K Γ G Q E : Type} [DecidableEq K] [Group G]

structure Instruction (K Γ G Q : Type) where
  source : Q
  target : Q
  action : Action K Γ
  weight : G

def Instruction.edge (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b) (i : Instruction K Γ G Q) :
    Edge G (Stores K) Q := actionEdge b digit hb i.source i.target i.weight i.action

inductive Run (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q) :
    List E → ((K → List Γ) × Q) → Prop
  | start : Run prog seed [] seed
  | step {s : List E} (e : E) (S T : K → List Γ) (h : (prog e).action.Rel S T) :
      Run prog seed s (S,(prog e).source) → Run prog seed (e::s) (T,(prog e).target)

variable (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q)
  (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

include hd hi in

theorem run_sound {s : List E} {c : Stores K × Q}
    (h : HistoryMachine.Run (fun e ↦ ((prog e).edge b digit hb).input)
      (fun e ↦ ((prog e).edge b digit hb).output) (encodeStores b digit seed.1,seed.2) s c) :
    ∃ S, encodeStores b digit S = c.1 ∧ Run prog seed s (S,c.2) := by
  induction h with
  | start => exact ⟨seed.1,rfl,Run.start⟩
  | @step s e x h ih =>
    obtain ⟨S,hS,hR⟩ := ih
    obtain ⟨T,hT,hr⟩ := action_sound b digit hb hd hi (prog e).source (prog e).target
      (prog e).weight (prog e).action x S hS.symm
    refine ⟨T,hT.symm,?_⟩
    simp only [Edge.input,Instruction.edge,actionEdge_inputState] at hR
    simpa only [Edge.output,Instruction.edge,actionEdge_outputState] using Run.step e S T hr hR

theorem run_complete {s : List E} {c : (K → List Γ) × Q} (h : Run prog seed s c) :
    HistoryMachine.Run (fun e ↦ ((prog e).edge b digit hb).input)
      (fun e ↦ ((prog e).edge b digit hb).output) (encodeStores b digit seed.1,seed.2)
      s (encodeStores b digit c.1,c.2) := by
  induction h with
  | start => exact HistoryMachine.Run.start
  | @step s e S T hr h ih =>
    obtain ⟨x,hS,hT⟩ := action_complete b digit hb (prog e).source (prog e).target
      (prog e).weight (prog e).action S T hr
    have hin : ((prog e).edge b digit hb).input x = (encodeStores b digit S,(prog e).source) := by
      apply Prod.ext hS
      exact actionEdge_inputState _ _ _ _ _ _ _
    have hout : ((prog e).edge b digit hb).output x = (encodeStores b digit T,(prog e).target) := by
      apply Prod.ext hT
      exact actionEdge_outputState _ _ _ _ _ _ _
    rw [← hout]
    apply HistoryMachine.Run.step (input := fun e ↦ ((prog e).edge b digit hb).input)
      (output := fun e ↦ ((prog e).edge b digit hb).output) e x
    rwa [hin]

def outputs (halt : Q) : Set G :=
  {g | ∃ s S, Run prog seed s (S,halt) ∧ g = HistoryMachine.value (fun e ↦ (prog e).weight) s}

end

open AffineStack MarkerMachine
variable {K Γ G Q E : Type} [DecidableEq K] [Group G]
  [Finite K] [Fintype Γ] [Finite Q] [Fintype E] [Group.IsFinitelyPresented G]
  (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q) (halt : Q)

theorem benign_outputs : IsBenign (Subgroup.closure (outputs prog seed halt)) := by
  classical
  let b : ℤ := Fintype.card Γ + 2
  let digit : Γ → ℤ := fun a ↦ ((Fintype.equivFin Γ a).val : ℤ) + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hd : ∀ a, 2 ≤ digit a ∧ digit a < b := by
    intro a
    have hh := (Fintype.equivFin Γ a).isLt
    dsimp [digit,b]
    constructor <;> omega
  have hi : Function.Injective digit := by
    intro a c h
    apply (Fintype.equivFin Γ).injective
    apply Fin.ext
    dsimp [digit] at h
    omega
  have : Group.IsFinitelyPresented (Stores K) := finitelyPresented_pi _ _
  have hp := RecordedMachine.benign_accepted (fun e ↦ (prog e).edge b digit hb)
    (encodeStores b digit seed.1,seed.2) halt
    (fun e ↦ action_finitelyPresented b digit hb (prog e).source (prog e).target
      (prog e).weight (prog e).action)
  have he : RecordedMachine.acceptedOutputs (fun e ↦ (prog e).edge b digit hb)
      (encodeStores b digit seed.1,seed.2) halt = outputs prog seed halt := by
    ext g
    constructor
    · rintro ⟨s,c,hs,hc,hg⟩
      obtain ⟨S,_,hR⟩ := run_sound prog seed b digit hb hd hi hs
      refine ⟨s,S,?_,?_⟩
      · rwa [hc] at hR
      · simpa only [Instruction.edge,actionEdge_weight] using hg
    · rintro ⟨s,S,hs,hg⟩
      refine ⟨s,(encodeStores b digit S,halt),run_complete prog seed b digit hb hs,rfl,?_⟩
      simpa only [Instruction.edge,actionEdge_weight] using hg
  rwa [he] at hp

end Higman.StackProgram

end OAI
