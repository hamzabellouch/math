import OAI.GroupTheory.UniversalGroup.MarkerMachine

namespace OAI

universe u v w x

namespace Higman.IntegerStack
variable {E : Type*}

def code (b : ℤ) (d : E → ℤ) : List E → ℤ
  | [] => 1
  | e :: s => b * code b d s + d e

@[simp] theorem code_nil (b : ℤ) (d : E → ℤ) : code b d [] = 1 := rfl
@[simp] theorem code_cons (b : ℤ) (d : E → ℤ) (e : E) (s : List E) :
    code b d (e :: s) = b * code b d s + d e := rfl

variable (b : ℤ) (d : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ d e ∧ d e < b)

include hd

lemma push_mod (e : E) (z : ℤ) : (b * z + d e) % b = d e := by
  rw [Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod,
    Int.emod_eq_of_lt (by have := (hd e).1; omega) (hd e).2]

include hb

lemma push_ne_empty (e : E) (z : ℤ) : b * z + d e ≠ 1 := by
  intro h
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,Int.emod_eq_of_lt (by omega) (by omega)] at he
  have := (hd e).1
  omega

lemma push_injective (hdinj : Function.Injective d) {e f : E} {z w : ℤ}
    (h : b * z + d e = b * w + d f) : e = f ∧ z = w := by
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,push_mod b d hd] at he
  have hef := hdinj he
  subst f
  refine ⟨rfl,?_⟩
  have hm : b * z = b * w := by omega
  exact mul_left_cancel₀ (by omega : b ≠ 0) hm

theorem decode_push (hdinj : Function.Injective d) (e : E) (z : ℤ) (s : List E) :
    b * z + d e = code b d s ↔ ∃ t, s = e :: t ∧ z = code b d t := by
  cases s with
  | nil => simp [push_ne_empty b d hb hd e z]
  | cons f t =>
    constructor
    · intro h
      obtain ⟨hef,hzt⟩ := push_injective b d hb hd hdinj h
      subst f
      exact ⟨t,rfl,hzt⟩
    · rintro ⟨u,hu,hz⟩
      cases hu
      simp [hz]

theorem code_injective (hdinj : Function.Injective d) : Function.Injective (code b d) := by
  intro s
  induction s with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | cons e t => exact False.elim (push_ne_empty b d hb hd e (code b d t) h.symm)
  | cons e s ih =>
    intro t h
    obtain ⟨u,rfl,hu⟩ := (decode_push b d hb hd hdinj e (code b d s) t).mp h
    exact congrArg (List.cons e) (ih hu)

theorem code_pos (s : List E) : 0 < code b d s := by
  induction s with
  | nil => simp
  | cons e s ih =>
    have hm : 0 < b * code b d s := mul_pos (by omega) ih
    have hh := (hd e).1
    rw [code_cons]
    omega

end Higman.IntegerStack

namespace Higman.HistoryMachine
variable {E : Type*} {C : Type*} {D : E → Type*}

inductive Run (input output : (e : E) → D e → C) (initial : C) : List E → C → Prop
  | start : Run input output initial [] initial
  | step {s : List E} (e : E) (z : D e) :
      Run input output initial s (input e z) → Run input output initial (e :: s) (output e z)

variable (input output : (e : E) → D e → C) (initial : C)

@[simp] theorem run_nil (c : C) : Run input output initial [] c ↔ c = initial := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Run.start

@[simp] theorem run_cons (e : E) (s : List E) (c : C) :
    Run input output initial (e :: s) c ↔
      ∃ z : D e, c = output e z ∧ Run input output initial s (input e z) := by
  constructor
  · intro h
    cases h with
    | step e z h => exact ⟨z,rfl,h⟩
  · rintro ⟨z,rfl,h⟩
    exact Run.step e z h

def Reach (b : ℤ) (digit : E → ℤ) (c : C) (history : ℤ) : Prop :=
  ∃ s, Run input output initial s c ∧ history = IntegerStack.code b digit s

variable (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

lemma reach_start : Reach input output initial b digit initial 1 := ⟨[],Run.start,rfl⟩

include hb hd hinj in

theorem reach_step_iff (hout : ∀ e, Function.Injective (output e)) (e : E) (z : D e)
    (h : ℤ) :
    Reach input output initial b digit (output e z) (b * h + digit e) ↔
      Reach input output initial b digit (input e z) h := by
  constructor
  · rintro ⟨s,hs,he⟩
    obtain ⟨t,rfl,ht⟩ := (IntegerStack.decode_push b digit hb hd hinj e h s).mp he
    obtain ⟨y,hy,hr⟩ := (run_cons input output initial e t (output e z)).mp hs
    have hzy : z = y := hout e hy
    subst y
    exact ⟨t,hr,ht⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨e :: s,Run.step e z hs,rfl⟩

variable {G : Type*} [Group G]

def value (weight : E → G) : List E → G
  | [] => 1
  | e :: s => value weight s * weight e

noncomputable def decoration (weight : E → G) (h : ℤ) : G := by
  classical
  exact if hh : ∃ s, h = IntegerStack.code b digit s then value weight hh.choose else 1

include hb hd hinj in
@[simp] theorem decoration_code (weight : E → G) (s : List E) :
    decoration b digit weight (IntegerStack.code b digit s) = value weight s := by
  classical
  unfold decoration
  split_ifs with h
  · have he : h.choose = s :=
      IntegerStack.code_injective b digit hb hd hinj h.choose_spec.symm
    rw [he]
  · exact False.elim (h ⟨s,rfl⟩)

include hb hd hinj in
lemma decoration_step (weight : E → G) (e : E) (z : D e) (h : ℤ)
    (hr : Reach input output initial b digit (input e z) h) :
    decoration b digit weight (b * h + digit e) = decoration b digit weight h * weight e := by
  obtain ⟨s,_,rfl⟩ := hr
  rw [← IntegerStack.code_cons,decoration_code b digit hb hd hinj,
    decoration_code b digit hb hd hinj]
  rfl

end Higman.HistoryMachine

namespace Higman.RecordedMachine

section
open MarkerMachine
abbrev Counter := Multiplicative ℤ

def scale (b : ℤ) : Counter →* Counter where
  toFun x := Multiplicative.ofAdd (b * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]

lemma scale_injective (b : ℤ) (hb : b ≠ 0) : Function.Injective (scale b) := by
  intro x y h
  change x.toAdd = y.toAdd
  exact mul_left_cancel₀ hb (congrArg Multiplicative.toAdd h)

variable {G T Q : Type u} [Group G]

def augment (c : T × Q) (h : ℤ) : (T × Counter) × Q := ((c.1,Multiplicative.ofAdd h),c.2)
def forget (c : (T × Counter) × Q) : T × Q := (c.1.1,c.2)
def history (c : (T × Counter) × Q) : ℤ := c.1.2.toAdd

@[simp] lemma forget_augment (c : T × Q) (h : ℤ) : forget (augment c h) = c := rfl
@[simp] lemma history_augment (c : T × Q) (h : ℤ) : history (augment c h) = h := rfl
@[simp] lemma augment_forget (c : (T × Counter) × Q) : augment (forget c) (history c) = c := rfl

variable [Group T]

def edge (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) : Edge G (T × Counter) Q where
  Domain := e.Domain × Counter
  inputLinear := e.inputLinear.prodMap (MonoidHom.id Counter)
  outputLinear := e.outputLinear.prodMap (scale b)
  input_injective := by
    intro x y h
    exact Prod.ext (e.input_injective (congrArg Prod.fst h)) (congrArg (fun p : T × Counter ↦ p.2) h)
  output_injective := by
    intro x y h
    exact Prod.ext (e.output_injective (congrArg Prod.fst h))
      (scale_injective b hb (congrArg Prod.snd h))
  inputOffset := (e.inputOffset,1)
  outputOffset := (e.outputOffset,Multiplicative.ofAdd digit)
  inputState := e.inputState
  outputState := e.outputState
  weight := e.weight

@[simp] lemma edge_input (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).input (d,h) = augment (e.input d) h.toAdd := by
  change ((e.inputLinear d, h) * (e.inputOffset, 1), e.inputState) = _
  simp only [Prod.mul_def, mul_one]
  rfl
@[simp] lemma edge_output (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).output (d,h) =
      augment (e.output d) (b * h.toAdd + digit) := rfl

variable {E : Type u} [Fintype E] (edges : E → Edge G T Q)
  (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)

noncomputable def edgeList : List (Edge G (T × Counter) Q) :=
  Finset.univ.toList.map (fun e ↦ edge (edges e) b (digit e) (by omega))

lemma mem_edgeList (e : E) : edge (edges e) b (digit e) (by omega) ∈ edgeList edges b digit hb := by
  classical
  exact List.mem_map.mpr ⟨e,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩

lemma of_mem_edgeList (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb) :
    ∃ e, a = edge (edges e) b (digit e) (by omega) := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨e,rfl⟩

variable (seed : T × Q)

def Forward (c : (T × Counter) × Q) : Prop :=
  HistoryMachine.Reach (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed b digit
    (forget c) (history c)

omit [Fintype E] in
lemma forward_start : Forward edges b digit seed (augment seed 1) :=
  HistoryMachine.reach_start _ _ _ _ _

variable (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

lemma output_injective (e : Edge G T Q) : Function.Injective e.output := by
  intro x y h
  exact e.output_injective (mul_right_cancel (congrArg Prod.fst h))

include hb hd hinj in
omit [Fintype E] in
lemma forward_edge (e : E) (d : (edges e).Domain) (h : ℤ) :
    Forward edges b digit seed (augment ((edges e).output d) (b*h + digit e)) ↔
      Forward edges b digit seed (augment ((edges e).input d) h) :=
  HistoryMachine.reach_step_iff _ _ _ b digit hb hd hinj
    (fun e ↦ output_injective (edges e)) e d h

include hd hinj in
lemma reach_implies_forward (c : (T × Counter) × Q)
    (hc : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c) :
    Forward edges b digit seed c := by
  induction hc with
  | start => exact forward_start edges b digit seed
  | forward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_output] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mpr
        (by simpa only [edge_input] using ih)
  | backward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_input] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mp
        (by simpa only [edge_output] using ih)

lemma run_implies_reach {s : List E} {c : T × Q}
    (hc : HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed s c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1)
      (augment c (IntegerStack.code b digit s)) := by
  induction hc with
  | start => exact MarkerMachine.Reach.start
  | @step s e d hr ih =>
    have hh := MarkerMachine.Reach.forward (seed := augment seed 1)
      (edge (edges e) b (digit e) (by omega)) (mem_edgeList edges b digit hb e)
      (d,Multiplicative.ofAdd (IntegerStack.code b digit s))
    rw [edge_input,edge_output] at hh
    exact hh ih

lemma forward_implies_reach (c : (T × Counter) × Q) (hc : Forward edges b digit seed c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c := by
  obtain ⟨s,hs,hh⟩ := hc
  have hr := run_implies_reach edges b digit hb seed hs
  rw [← hh,augment_forget] at hr
  exact hr

include hd hinj in

theorem reach_iff_forward (c : (T × Counter) × Q) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c ↔
      Forward edges b digit seed c :=
  ⟨reach_implies_forward edges b digit hb seed hd hinj c,
    forward_implies_reach edges b digit hb seed c⟩

end

open MarkerMachine DecoratedMarker MarkerEmbedding
variable {G T Q E : Type u} [Group G] [Group T] [Fintype E]
  (edges : E → Edge G T Q) (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (seed : T × Q) (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

noncomputable def decoration (c : (T × Counter) × Q) : G :=
  HistoryMachine.decoration b digit (fun e ↦ (edges e).weight) (history c)

include hd hinj in
lemma decoration_edge (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb)
    (d : a.Domain) (hr : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) (a.input d)) :
    decoration edges b digit (a.output d) = decoration edges b digit (a.input d) * a.weight := by
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  obtain ⟨d,h⟩ := d
  have hf := reach_implies_forward edges b digit hb seed hd hinj _ hr
  rw [edge_input] at hf ⊢
  rw [edge_output]
  exact HistoryMachine.decoration_step (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed b digit hb hd hinj
    (fun e ↦ (edges e).weight) e d h.toAdd hf

include hb hd hinj in

theorem benign_forward [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T] [Finite Q]
    (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (decoratedSubgroup (decoration edges b digit) {c | Forward edges b digit seed c}) := by
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have he : {c | MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c} =
      {c | Forward edges b digit seed c} := by
    ext c
    exact reach_iff_forward edges b digit hb seed hd hinj c
  rw [← he]
  apply MarkerMachine.benign _ _ _ _ (decoration_edge edges b digit hb seed hd hinj)
  intro a ha
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  have := hD e
  exact finitelyPresented_prod

end Higman.RecordedMachine

namespace Higman.MarkerEmbedding
open Monoid Coprod DecoratedMarker
variable {G T : Type u} {Q : Type*} [Group G] [Group T]

def coefficientProjection : Base G T Q →* G := Coprod.lift (MonoidHom.fst G T) 1

@[simp] lemma projection_coefficient (g : G) :
    coefficientProjection (coefficient g : Base G T Q) = g := by
  simp [coefficientProjection,coefficient]
@[simp] lemma projection_translation (t : T) :
    coefficientProjection (translation t : Base G T Q) = 1 := by
  simp [coefficientProjection,translation]
@[simp] lemma projection_marker (t : T) (q : Q) :
    coefficientProjection (marker t q : Base G T Q) = 1 := by
  simp [coefficientProjection,marker,translation]

lemma projection_surjective : Function.Surjective (coefficientProjection : Base G T Q →* G) :=
  fun g ↦ ⟨coefficient g,projection_coefficient g⟩

variable {Q : Type u}

theorem benign_output [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]
    (v : T × Q → G) (V : Set (T × Q)) (hR : IsBenign (decoratedSubgroup v V)) (q : Q) :
    IsBenign (Subgroup.closure (v '' {c | c ∈ V ∧ c.2 = q})) := by
  have : Group.IsFinitelyPresented (G × T) := finitelyPresented_prod
  let f : Base G T Unit →* Base G T Q := embedding (MonoidHom.id T) (fun _ ↦ 1)
    (fun _ ↦ q) (fun _ ↦ 1)
  have hi : Function.Injective (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q)) :=
    index_injective _ Function.injective_id _ _ (Function.injective_of_subsingleton _)
  have hB := (hR.comap f).map_surjective
    (coefficientProjection : Base G T Unit →* G)
      (projection_surjective (G := G) (T := T) (Q := Unit))
  dsimp only [f] at hB
  rw [comap_decoratedSubgroup _ Function.injective_id _ _ _ hi,
    decoratedSubgroup_eq_closure,MonoidHom.map_closure] at hB
  have he : (coefficientProjection : Base G T Unit →* G) ''
      ((fun x : T × Unit ↦ coefficient
        (pullDecoration (MonoidHom.id T) (fun _ ↦ 1) (fun _ ↦ q) (fun _ ↦ 1) v x) *
          marker x.1 x.2) ''
        (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q) ⁻¹' V)) =
      v '' {c | c ∈ V ∧ c.2 = q} := by
    rw [Set.image_image]
    ext g
    constructor
    · rintro ⟨⟨t,p⟩,ht,rfl⟩
      refine ⟨(t,q),⟨?_,rfl⟩,?_⟩
      · simpa [index] using ht
      · simp [pullDecoration,index]
    · rintro ⟨⟨t,r⟩,⟨hc,hq⟩,rfl⟩
      change r = q at hq
      subst r
      refine ⟨(t,()),?_,?_⟩
      · simpa [index] using hc
      · simp [pullDecoration,index]
  rw [he] at hB
  exact hB

end Higman.MarkerEmbedding

namespace Higman.RecordedMachine
open MarkerMachine
variable {G T Q E : Type u} [Group G] [Group T]
  (edges : E → Edge G T Q) (seed : T × Q) (halt : Q)

def acceptedOutputs : Set G :=
  {g | ∃ s c, HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed s c ∧ c.2 = halt ∧ g = HistoryMachine.value (fun e ↦ (edges e).weight) s}

variable [Fintype E] [Finite Q] [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]

theorem benign_accepted (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (Subgroup.closure (acceptedOutputs edges seed halt)) := by
  classical
  let b : ℤ := Fintype.card E + 2
  let digit : E → ℤ := fun e ↦ ((Fintype.equivFin E e).val : ℤ) + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hd : ∀ e, 2 ≤ digit e ∧ digit e < b := by
    intro e
    have hh := (Fintype.equivFin E e).isLt
    dsimp [digit,b]
    constructor <;> omega
  have hi : Function.Injective digit := by
    intro e f h
    apply (Fintype.equivFin E).injective
    apply Fin.ext
    dsimp [digit] at h
    omega
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have hp := MarkerEmbedding.benign_output (decoration edges b digit)
    {c | Forward edges b digit seed c}
    (benign_forward edges b digit hb seed hd hi hD) halt
  have he : decoration edges b digit ''
      {c | c ∈ {c | Forward edges b digit seed c} ∧ c.2 = halt} =
      acceptedOutputs edges seed halt := by
    ext g
    constructor
    · rintro ⟨c,⟨⟨s,hs,hh⟩,hc⟩,rfl⟩
      refine ⟨s,forget c,hs,hc,?_⟩
      dsimp [decoration]
      rw [hh,HistoryMachine.decoration_code b digit hb hd hi]
    · rintro ⟨s,c,hs,hc,rfl⟩
      refine ⟨augment c (IntegerStack.code b digit s),⟨?_,hc⟩,?_⟩
      · exact ⟨s,hs,rfl⟩
      · exact HistoryMachine.decoration_code b digit hb hd hi _ s
  rwa [he] at hp

end Higman.RecordedMachine

namespace Higman

theorem finitelyPresented_pi (I : Type u) [Finite I] (G : Type v) [Group G]
    [Group.IsFinitelyPresented G] : Group.IsFinitelyPresented (I → G) := by
  apply Finite.induction_empty_option _ _ _ I
  · intro A B e ih
    have := ih
    exact Group.IsFinitelyPresented.equiv (MulEquiv.arrowCongr e (MulEquiv.refl G))
  · infer_instance
  · intro A _ ih
    have := ih
    have : Group.IsFinitelyPresented (G × (A → G)) := finitelyPresented_prod
    let e : (Option A → G) ≃* G × (A → G) :=
      { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }
    exact Group.IsFinitelyPresented.equiv e.symm

end Higman

end OAI
