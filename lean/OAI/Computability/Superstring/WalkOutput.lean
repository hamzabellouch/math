import OAI.Computability.Superstring.SchedulerMachine

namespace OAI

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α]
def letter (s t : List α) : List α := if s.length<t.length then [t.reverse.headD default] else []
def output (P : Walk α) : List α := (P.zip P.tail).flatMap (fun q => letter q.1 q.2)
@[simp] theorem output_nil : output ([] : Walk α)=[] := rfl
@[simp] theorem output_singleton (s : List α) : output [s]=[] := rfl
@[simp] theorem output_cons_cons (s t : List α) (P : Walk α) :
    output (s::t::P) = letter s t ++ output (t::P) := by simp only [output,List.tail_cons,List.zip_cons_cons,List.flatMap_cons]
@[simp] theorem length_letter (s t : List α) : (letter s t).length = if s.length<t.length then 1 else 0 := by
  unfold letter; split <;> rfl
@[simp] theorem length_output (P : Walk α) : (output P).length = cost P := by
  induction P using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons s t P _ ih => rw [output_cons_cons,List.length_append,length_letter,ih,cost_cons_cons]
theorem letter_up (s : List α) (a : α) : letter s (s++[a])=[a] := by
  simp [letter,List.reverse_append]
theorem letter_down (t : List α) (a : α) : letter (a::t) t=[] := by simp [letter]

theorem visited_output {V : Set (List α)} {s : List α} {P : Walk α} (h : Valid V (s::P))
    {w : List α} (hw : w ∈ s::P) : w <:+: s++output (s::P) := by
  induction P generalizing s with
  | nil => have he := List.mem_singleton.mp hw; subst w; simp
  | cons t P ih =>
    obtain ⟨he,hchain⟩ := List.isChain_cons_cons.mp h.2.2
    rcases List.mem_cons.mp hw with rfl|hw
    · exact List.infix_append_left
    · have ht : Valid V (t::P) := ⟨by simp,fun w hw => h.2.1 w (List.mem_cons_of_mem _ hw),hchain⟩
      have hv := ih ht hw
      rw [output_cons_cons]
      rcases he with ⟨a,rfl⟩|⟨a,rfl⟩
      · simpa only [letter_up,List.append_assoc] using hv
      · simpa only [letter_down,List.nil_append,List.cons_append] using (List.infix_cons hv (a:=a))

theorem rooted_output {V : Set (List α)} {P : Walk α} (h : Runs V [] [] P) :
    ∀ w ∈ P, w <:+: output P := by
  cases P with
  | nil => exact False.elim (h.1.1 rfl)
  | cons s P =>
    have hs : s=[] := by simpa using h.2.1
    subst s
    intro w hw
    simpa using visited_output h.1 hw

variable [Coded α]
@[fun_prop] theorem poly_letter : Poly (fun q : List α × List α => letter q.1 q.2) := by
  unfold letter
  apply CollectionCode.poly_cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_output : Poly (output : Walk α → List α) := by
  unfold output
  exact BitCode.Poly.flatMapFn (f := fun q : Walk α × (List α × List α) => letter q.2.1 q.2.2) (by fun_prop) (by fun_prop)
end Superstring.WalkCode


namespace Superstring.CollectionCode.Model
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
variable {V : Set (List α)} {X : Env α} {C : LayerCollection V G} (h : Model X C)
include h in
theorem tour_spec_general (vs : Walk α) (hv : V={w | w ∈ vs})
    (closed : SubstringClosed V) (nil_mem : ([] : List α) ∈ V)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    Runs V [] [] (tour (vs,X,M)) ∧ cost (tour (vs,X,M)) ≤ ((gs X).map (charge X)).sum ∧
    ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, w ∈ tour (vs,X,M) := by
  subst V
  obtain ⟨hp,hc,hcov⟩ := h.tour_spec closed nil_mem supply M len
  exact ⟨hp,hc,fun i w hw => hcov (h.encode i) (h.id_mem i) w ((h.content_iff i w).mpr hw)⟩
include h in
omit [Coded α] in
theorem charge_sum [Fintype G] : ((gs X).map (charge X)).sum = 2*∑ g, C.size g*C.period g := by
  classical
  rw [← List.sum_toFinset _ h.nodup,Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun g _ => h.group g)
  · intro g _; exact List.mem_toFinset.mpr ((h.groups _).mpr ⟨g,rfl⟩)
  · intro a _ b _ he; exact h.group_inj he
  · intro j hj
    obtain ⟨g,hg⟩ := (h.groups _).mp (List.mem_toFinset.mp hj)
    exact ⟨g,Finset.mem_univ _,hg⟩
  · intro g _; simp only [charge,h.size,h.per_eq]
end Superstring.CollectionCode.Model


namespace Superstring.ThreadArray
open BitCode Hierarchical CollectionCode
variable {α : Type} [Coded α] [Inhabited α] [LinearOrder α]
def environment (K : Code α) : Env α :=
  (((List.range K.1.length).map (data K),groups K),K.1.length)

@[simp] theorem environment_rows (K : Code α) : (environment K).1.1.length = K.1.length := by
  simp only [environment,List.length_map,List.length_range]
@[simp] theorem environment_stride (K : Code α) : stride (environment K) = K.1.length := rfl

theorem environment_data (K : Code α) (g : ℕ) (hg : g < K.1.length) :
    CollectionCode.data (environment K) g = data K g := by
  simp only [CollectionCode.data,environment,List.getElem?_map,List.getElem?_range hg,
    Option.map_some,Option.getD_some]

noncomputable def model {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    CollectionCode.Model (environment K) (collection h closed) where
  group := fun g => g.val.val
  group_inj := by intro g d hd; exact Subtype.ext (Fin.ext hd)
  groups := by
    intro j
    change j ∈ groups K ↔ _
    simp only [groups,List.mem_filter,List.mem_range,equal,decide_eq_true_eq]
    constructor
    · rintro ⟨hj,hr⟩
      exact ⟨⟨⟨j,hj⟩,hr⟩,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨g.val.isLt,g.property⟩
  nodup := List.Pairwise.filter _ List.nodup_range
  bound := by intro g; simpa only [environment_rows] using g.val.isLt
  size := by intro g; rw [environment_data K _ g.val.isLt]; exact data_size h g.val
  capacity := by
    intro g
    change Fintype.card (C.Aligned (C.text g.val)) ≤ K.1.length
    rw [← aligned_length h]
    exact aligned_length_le K g.val.val
  rep := by
    intro g i
    rw [environment_data K _ g.val.isLt]
    exact data_represents h closed g.val i
  phase_eq := by
    intro g
    unfold CollectionCode.phase
    rw [environment_data K _ g.val.isLt]
    exact RotationCode.phase_eq_distinguished (collection h closed) g (period_spec h g.val).1
      (layerWord K g.val.val) (length_layerWord h g.val) (text_layerWord h g.val)

@[fun_prop] theorem poly_environment : Poly (environment (α:=α)) := by
  have hm : Poly (fun K : Code α => (List.range K.1.length).map (data K)) :=
    BitCode.Poly.mapFn (f := fun q : Code α × ℕ => data q.1 q.2) poly_data (by fun_prop)
  unfold environment
  fun_prop
end Superstring.ThreadArray


namespace Superstring.Executable
open BitCode Hierarchical ThreadArray
variable {α : Type} [Inhabited α] [LinearOrder α] [Coded α]
abbrev code (S : List (List α)) : ThreadArray.Code α := (Computable.downWords S,Computable.edges S)
def context (S : List (List α)) : CollectionCode.Context α :=
  (Computable.vertices S,ThreadArray.environment (code S),Computable.countDepth S)
def solve (S : List (List α)) : List α := WalkCode.output (CollectionCode.tour (context S))
@[fun_prop] theorem poly_code : Poly (code : List (List α) → ThreadArray.Code α) := by unfold code; fun_prop
@[fun_prop] theorem poly_context : Poly (context : List (List α) → CollectionCode.Context α) :=
  Computable.poly_vertices.pair ((ThreadArray.poly_environment.comp poly_code).pair Computable.poly_countDepth)
@[fun_prop] theorem poly_solve (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (solve : List (List α) → List α) := by
  unfold solve
  apply (WalkCode.poly_output (α:=α)).comp (f := fun S : List (List α) => CollectionCode.tour (context S))
  exact (CollectionCode.poly_tour hlt).comp (f := context) poly_context

theorem represents (S : List (List α)) : ThreadArray.Represents (code S) (Computable.arrayThreading S) :=
  ⟨fun _ => rfl,fun _ => rfl⟩

omit [Inhabited α] [Coded α] in
theorem vertices_eq (S : List (List α)) : ((Input.data S).vertices : Set (List α)) = {w | w ∈ Computable.vertices S} := by
  ext w
  change w ∈ Input.vertices S ↔ w ∈ Computable.vertices S
  rw [← Computable.vertices_eq S,List.mem_toFinset]

omit [Inhabited α] [Coded α] in
theorem length_vertices (S : List (List α)) (w : List α) (hw : w ∈ Computable.vertices S) :
    w.length ≤ Computable.countDepth S := by
  have h := le_maxFold ((Computable.vertices S).map List.length) 0 (List.mem_map.mpr ⟨w,hw,rfl⟩)
  unfold Computable.countDepth
  omega

omit [Inhabited α] [Coded α] in
theorem closed (S : List (List α)) : SubstringClosed ((Input.data S).vertices : Set (List α)) :=
  Input.closed S

theorem histogram (S : List (List α)) (s : List α) (hs : s ≠ []) :
    Fintype.card (Family.Occurrence (ThreadArray.collection (represents S) (closed S)).layerAt s) =
      (Input.data S).count s := by
  rw [ThreadArray.collection_histogram,← Threading.card_recorded,Computable.arrayThreading_recorded_count S hs]

theorem supply (S : List (List α)) : (ThreadArray.collection (represents S) (closed S)).RecordSupply := by
  apply LayerCollection.recordSupply_of_histogram _ (Input.data S) (Counts.Data.input_wellFormed S) rfl
  · exact histogram S
  · intro g; exact (ThreadArray.period_spec (represents S) g.val).1

theorem solve_spec (S : List (List α)) :
    (∀ s ∈ S, s <:+: solve S) ∧ (solve S).length ≤ 2*(Input.data S).weight := by
  classical
  let C := ThreadArray.collection (represents S) (closed S)
  let h := ThreadArray.model (represents S) (closed S)
  obtain ⟨hp,hc,hcov⟩ := h.tour_spec_general (Computable.vertices S) (vertices_eq S)
    (closed S) (Counts.Data.input_wellFormed S).empty_mem (supply S) (Computable.countDepth S) (length_vertices S)
  have hbudget : ((CollectionCode.gs (ThreadArray.environment (code S))).map
      (CollectionCode.charge (ThreadArray.environment (code S)))).sum = 2*(Input.data S).weight := by
    rw [h.charge_sum]
    have hh := ThreadArray.collection_budget (represents S) (closed S)
    have he : (∑ g, C.size g*C.period g) = (code S).1.length := by
      simpa only [C,Nat.mul_comm] using hh
    change 2*(∑ g, C.size g*C.period g)=_
    rw [he]
    exact congrArg (2*·) (Computable.downWords_length S)
  constructor
  · apply (Input.core_superstring_iff S (solve S)).mp
    intro s hs
    have hsV := Input.required_mem hs
    have hsne := (Input.mem_core.mp hs).2.1
    have hcount := (Input.data S).required_le_count hsV hsne hs
    have hn : 0 < Fintype.card (Family.Occurrence C.layerAt s) := by
      rw [show Fintype.card (Family.Occurrence C.layerAt s)=(Input.data S).count s from histogram S s hsne]
      omega
    obtain ⟨o⟩ := Fintype.card_pos_iff.mp hn
    let L := C.layerAt o.1
    have hpre : s <+: textWord (C.text o.1.1) o.2.val.val (L.last o.2.val.val) :=
      (L.records_iff_prefix s o.2.val.val).mp o.2.property
    have hv := hcov o.1 _ ⟨o.2.val.val,L.last o.2.val.val,L.first_le_last o.2.val.val,le_rfl,rfl⟩
    exact hpre.isInfix.trans (WalkCode.rooted_output hp _ hv)
  · unfold solve
    rw [WalkCode.length_output]
    exact hc.trans_eq hbudget
end Superstring.Executable

end OAI
