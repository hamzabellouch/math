import OAI.Computability.Superstring.HostNormalized

namespace OAI

namespace Superstring.HostCode
open BitCode Hierarchical WalkCode LayerArray
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

def completePool (U : List α) (Z : List ℕ) (E : List (Entry α))
    (D : List (LayerData α)) : List (Walk α) :=
  (requestPool U E).map (saturateAll ((U,Z)::D))

theorem completePool_complete {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (Z : List ℕ) (hD : Represents U Z D)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (A' : κ → ℤ → α) (L : ∀ i, Layer V (A' i) (H (g i)).period)
    (D' : κ → LayerData α) (I : List κ) (hne : I ≠ [])
    (hL : ∀ i ∈ I, Represents (D' i).1 (D' i).2 (L i))
    (hp : ∀ i ∈ I, Function.Periodic (A' i) ((H (g i)).period : ℤ))
    (hc : ∀ i ∈ I, (L i).Content = (R i).layer.Content) :
    ∃ P ∈ completePool U Z (I.map (entryOf H g R W tag)) (I.map D'),
      Runs V [] [] P ∧ cost P ≤ 2*(q+(I.map (fun i => (H (g i)).period)).sum) ∧
      (∀ w ∈ D.Content, w ∈ P) ∧ ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ P := by
  obtain ⟨P,hPin,hP,hPc,hPD,hPi⟩ := requestPool_complete closed D hq per letters H g R W tag htag
    U hD.length_eq hD.text_eq hW hWt child_letters different I hne
  let A₁ : Option κ → ℤ → α := fun i => i.elim A A'
  let p₁ : Option κ → ℕ := fun i => i.elim q (fun j => (H (g j)).period)
  let L₁ : ∀ i, Layer V (A₁ i) (p₁ i) := fun i => by cases i with
    | none => exact D
    | some i => exact L i
  let D₁ : Option κ → LayerData α := fun i => i.elim (U,Z) D'
  let I₁ : List (Option κ) := none :: I.map some
  obtain ⟨hS,hSc,_,hSv⟩ := saturateAll_spec closed A₁ p₁ L₁ D₁ I₁
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hD
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact hL j hj)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hq
        · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi; exact (H (g j)).positive)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact per
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact hp j hj)
    hP
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hPD
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
          change ∃ w ∈ (L j).Content, w ∈ P
          rw [hc j hj]
          exact hPi j hj)
  have hm : I₁.map D₁ = (U,Z)::I.map D' := by simp only [I₁,List.map_cons,List.map_map,D₁,Option.elim_none,Option.elim_some,Function.comp_def]
  have hsum : (I₁.map p₁).sum = q+(I.map (fun i => (H (g i)).period)).sum := by
    simp only [I₁,List.map_cons,List.sum_cons,List.map_map,p₁,Option.elim_none,Option.elim_some,Function.comp_def]
  rw [hm] at hS hSc hSv
  rw [hsum] at hSc
  refine ⟨_,List.mem_map.mpr ⟨P,hPin,rfl⟩,hS,by omega,?_,?_⟩
  · exact hSv none (List.mem_cons_self ..)
  · intro i hi
    exact hSv (some i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩))

variable [Coded α]
@[fun_prop] theorem poly_completePool : Poly (fun t : List α × List ℕ × List (Entry α) × List (LayerData α) =>
    completePool t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  unfold completePool
  exact BitCode.Poly.mapFn
    (f := fun t : (List α × List ℕ × List (Entry α) × List (LayerData α)) × Walk α =>
      saturateAll ((t.1.1,t.1.2.1)::t.1.2.2.2) t.2)
    (by fun_prop) (by fun_prop)
end Superstring.HostCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
abbrev Request := ℕ × ℕ × List ℕ × RecordCode.Code
namespace Request
def source (r : Request) := r.1
def target (r : Request) := r.2.1
def members (r : Request) := r.2.2.1
def code (r : Request) := r.2.2.2
def reserve (X : Env α) (r : Request) := 2*(r.members.length*per X r.source)
def ids (X : Env α) (r : Request) := r.members.map (fun i => r.source*stride X+i)
def entry (X : Env α) (r : Request) (i : ℕ) : HostCode.Entry α :=
  (r.source,PeriodWord.shift (data X r.source).1 (RecordCode.offset r.code),
    RecordCode.start r.code+RecordCode.offset r.code,
    RecordCode.stop r.code+RecordCode.offset r.code,
    GeoCode.first (exits (data X r.source) i) (RecordCode.start r.code)+RecordCode.offset r.code)
end Request

structure RequestWitness {X : Env α} {C : LayerCollection V G} (h : Model X C) (r : Request) where
  source : G
  target : C.Id
  source_eq : h.group source = r.source
  target_eq : h.encode target = r.target
  record : (C.layerAt target).Record (C.text source)
  offset : record.offset = RecordCode.offset r.code
  start : record.start = RecordCode.start r.code
  stop : record.stop = RecordCode.stop r.code
  foreign : C.text source ≠ fun x => C.text target.1 (x+record.offset)
  nonempty : r.members ≠ []
  nodup : r.members.Nodup
  bound : ∀ i ∈ r.members, i < C.size source
  long : ∀ i ∈ r.members, record.start+C.period source < (h.natLayer source i).first record.start
  margin : ∀ i ∈ r.members, (h.natLayer source i).last record.start < record.stop-C.period source

def ValidRequest {X : Env α} {C : LayerCollection V G} (h : Model X C) (r : Request) : Prop :=
  Nonempty (RequestWitness h r)

namespace RequestWitness
variable {X : Env α} {C : LayerCollection V G} {h : Model X C} {r : Request} (w : RequestWitness h r)
include w in
theorem later : per X r.source < per X (owner X r.target) := by
  obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil r.members w.nonempty
  have hl := w.long i hi
  have hm := w.margin i hi
  have hh := (h.natLayer w.source i).first_le_last w.record.start
  have hr := w.record.length_lt (C.positive w.source) (C.positive w.target.1)
    (C.periodic w.source) (C.periodic w.target.1) w.foreign
  rw [← w.source_eq,← w.target_eq,h.owner_eq,h.per_eq,h.per_eq]
  omega

def hosted : HostedGroup (C.layerAt w.target) where
  text := fun x => C.text w.source (x-w.record.offset)
  period := C.period w.source
  positive := C.positive w.source
  periodic := fun x => by simpa only [add_sub_right_comm] using C.periodic w.source (x-w.record.offset)
  start := w.record.start+w.record.offset
  stop := w.record.stop+w.record.offset
  first_le := w.record.first_le
  le_last := w.record.le_last
  agree := by
    intro x hx hy
    have hh := w.record.agree (x-w.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply w.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x+w.record.offset)

def request (i : {j // j ∈ r.members}) : w.hosted.Request where
  layer := (h.natLayer w.source i.val).translate w.record.offset
  stop := (h.natLayer w.source i.val).first w.record.start+w.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted,Layer.translate_last,add_sub_cancel_right]
    have hh := (h.natLayer w.source i.val).first_le_last w.record.start
    omega
  long := by
    have hh := w.long i.val i.property
    change w.record.start+w.record.offset+C.period w.source < _
    omega
  margin := by
    have hh := w.margin i.val i.property
    have hf := (h.natLayer w.source i.val).first_le_last w.record.start
    change _ ≤ w.record.stop+w.record.offset-C.period w.source
    omega

theorem data_rep (i : {j // j ∈ r.members}) :
    Represents (UpperCode.lookup (book X) (r.source*stride X+i.val)).1
      (UpperCode.lookup (book X) (r.source*stride X+i.val)).2 (h.natLayer w.source i.val) := by
  rw [← w.source_eq,lookup_encode X _ _ (h.bound _) (lt_of_lt_of_le (w.bound i.val i.property) (h.capacity _))]
  exact h.nat_rep w.source (w.bound i.val i.property)

theorem entry_eq (i : {j // j ∈ r.members}) : Request.entry X r i.val =
    (r.source,PeriodWord.shift (data X r.source).1 w.record.offset,
      w.hosted.start,w.hosted.stop,(w.request i).stop) := by
  simp only [Request.entry,← w.source_eq,← w.offset,← w.start,← w.stop,hosted,request]
  simp only [GeoCode.first,(h.nat_rep w.source (w.bound i.val i.property)).exit_eq,Layer.first]
end RequestWitness
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
abbrev Plan (α : Type) := Walk α × List (BlockClose.Block α) × List Request
def planBudget (X : Env α) (o : Plan α) := cost o.1+(o.2.1.map Block.reserve).sum+(o.2.2.map (Request.reserve X)).sum
def hardPlan (X : Env α) (g cut : ℕ) (v : UpperCode.Param) : Plan α :=
  let o := hard X g cut v
  (o.1,o.2.1,if o.2.2.isEmpty then [] else [(g,v.2.1,o.2.2,v.2.2)])
def Covered (X : Env α) (o : Plan α) (i : ℕ) :=
  (∀ w ∈ ls X i, w ∈ o.1) ∨ (∃ b ∈ o.2.1, i ∈ b.members) ∨ ∃ r ∈ o.2.2, i ∈ r.ids X

def GoodPlan {X : Env α} {C : LayerCollection V G} (h : Model X C) (o : Plan α) : Prop :=
  Runs V [] [] o.1 ∧ (∀ b ∈ o.2.1, ValidBlock V (ids X) (ls X) (owner X) (per X) (rank X) b) ∧
    ∀ r ∈ o.2.2, ValidRequest h r
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem hardPlan_spec (closed : SubstringClosed V) (g : G) (cut : ℕ) (v : UpperCode.Param)
    (hcut : cut < C.size g) (hv : v.2.1 ∈ ids X)
    (ht : UpperCode.test (data X (h.group g)) (book X) cut (phase X (h.group g)) v = true)
    (hf : UpperCode.foreign (data X (h.group g)) (book X) v = true) :
    let o := hardPlan X (h.group g) cut v
    GoodPlan h o ∧ planBudget X o ≤ 2*((C.size g-cut)*C.period g) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val → Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ o.2.2, r.source = h.group g) ∧ o.2.2.length ≤ 1 := by
  obtain ⟨hr,hb,hblocks,hcov,hsub,d,R,hd,hoff,ha,hb',hne,hm⟩ := h.hard_spec closed g cut v hcut hv ht hf
  let p := hard X (h.group g) cut v
  have hsub' : p.2.2.Sublist (UpperCode.upper (C.size g) cut) := hsub
  have hlength : p.2.2.length*C.period g = p.2.2.length*per X (h.group g) := by rw [h.per_eq]
  by_cases he : p.2.2 = []
  · have hoja : hardPlan X (h.group g) cut v = (p.1,p.2.1,[]) := by simp only [hardPlan,p,he,List.isEmpty_nil,↓reduceIte]
    rw [hoja]
    refine ⟨⟨hr,hblocks,by simp⟩,?_,?_,by simp,by simp⟩
    · simpa only [planBudget,DistributeCode.budget,show (hard X (h.group g) cut v).2.2=[] from he,
        List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using hb
    · intro i hi
      rcases hcov i hi with hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · simp only [show (hard X (h.group g) cut v).2.2=[] from he,List.not_mem_nil] at hh
  · let r : Request := (h.group g,v.2.1,p.2.2,v.2.2)
    have hoja : hardPlan X (h.group g) cut v = (p.1,p.2.1,[r]) := by
      simp only [hardPlan,show (hard X (h.group g) cut v).2.2=p.2.2 from rfl,
        List.isEmpty_iff,he,↓reduceIte,r,p]
    have hw : ValidRequest h r := ⟨{
      source := g, target := d, source_eq := rfl, target_eq := hd, record := R,
      offset := hoff, start := ha, stop := hb', foreign := hne, nonempty := he,
      nodup := (List.Nodup.filter _ List.nodup_range).sublist hsub',
      bound := fun i hi => (UpperCode.mem_upper _ _ i).mp (hsub'.subset hi) |>.2,
      long := fun i hi => (hm i hi).1,
      margin := fun i hi => (hm i hi).2 }⟩
    rw [hoja]
    refine ⟨⟨hr,hblocks,?_⟩,?_,?_,?_,by simp⟩
    · intro s hs
      exact List.mem_singleton.mp hs ▸ hw
    · simpa only [planBudget,List.map_singleton,List.sum_singleton,Request.reserve,Request.members,Request.source,r,
        h.per_eq,DistributeCode.budget] using hb
    · intro i hi
      rcases hcov i hi with hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨r,List.mem_singleton_self _,List.mem_map.mpr ⟨i.val,hh,rfl⟩⟩)
    · intro s hs
      exact List.mem_singleton.mp hs ▸ rfl
end Model
end Superstring.CollectionCode

end OAI
