import OAI.Computability.Superstring.FibreSelect

namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def pick (X : Env α) (I : List ℕ) : ℕ := firstGood I (fun g => I.all (fun j => lessEq (per X g) (per X j)))
def without (I : List ℕ) (g : ℕ) : List ℕ := I.filter (fun i => !(equal i g))
def inRequests (X : Env α) (g : ℕ) (R : List Request) : List Request := R.filter (fun r => equal (owner X r.target) g)
def restRequests (X : Env α) (g : ℕ) (R : List Request) : List Request := R.filter (fun r => !(equal (owner X r.target) g))
def charge (X : Env α) (g : ℕ) : ℕ := 2*((data X g).2.length*per X g)
abbrev State (α : Type) := List ℕ × Plan α
def advance (vs : Walk α) (X : Env α) (M : ℕ) (s : State α) : State α :=
  if s.1.isEmpty then s else
  let g := pick X s.1
  let o := process vs X g M (inRequests X g s.2.2.2)
  (without s.1 g,join s.2.1 o.1,s.2.2.1++o.2.1,restRequests X g s.2.2.2++o.2.2)

omit [Inhabited α] [LinearOrder α] in
theorem pick_spec (X : Env α) (I : List ℕ) (hn : I ≠ []) :
    pick X I ∈ I ∧ ∀ j ∈ I, per X (pick X I) ≤ per X j := by
  have hne : I.toFinset.Nonempty := by
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨i,List.mem_toFinset.mpr hi⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image I.toFinset (per X) hne
  have hh := firstGood_mem I (fun g => I.all (fun j => lessEq (per X g) (per X j)))
    ⟨i,List.mem_toFinset.mp hi,List.all_eq_true.mpr (fun j hj => by
      simpa only [lessEq,decide_eq_true_eq] using hmin j (List.mem_toFinset.mpr hj))⟩
  exact ⟨hh.1,fun j hj => of_decide_eq_true (List.all_eq_true.mp hh.2 j hj)⟩
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_without (I : List ℕ) (g i : ℕ) : i ∈ without I g ↔ i ∈ I ∧ i ≠ g := by simp [without,equal]
omit [Inhabited α] [LinearOrder α] in
theorem without_lt (I : List ℕ) (g : ℕ) (hg : g ∈ I) : (without I g).length < I.length := by
  exact List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [equal]⟩
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_inRequests (X : Env α) (g : ℕ) (R : List Request) (r : Request) :
    r ∈ inRequests X g R ↔ r ∈ R ∧ owner X r.target=g := by simp [inRequests,equal]
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_restRequests (X : Env α) (g : ℕ) (R : List Request) (r : Request) :
    r ∈ restRequests X g R ↔ r ∈ R ∧ owner X r.target≠g := by simp [restRequests,equal]
omit [Inhabited α] [LinearOrder α] in
theorem sum_partition {δ : Type} (R : List δ) (p : δ → Bool) (f : δ → ℕ) :
    ((R.filter p).map f).sum+((R.filter (fun r => !(p r))).map f).sum=(R.map f).sum := by
  induction R with
  | nil => simp
  | cons r R ih => cases hp : p r <;> simp only [List.filter_cons,hp,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons] <;> omega
omit [Inhabited α] [LinearOrder α] in
theorem charge_remove (X : Env α) (I : List ℕ) (hn : I.Nodup) (g : ℕ) (hg : g ∈ I) :
    charge X g+((without I g).map (charge X)).sum=(I.map (charge X)).sum := by
  induction I with
  | nil => simp at hg
  | cons a I ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hg with rfl|hg
    · have he : without I g = I := by
        apply List.filter_eq_self.mpr
        intro j hj
        simpa only [Bool.not_eq_true',equal,decide_eq_false_iff_not] using (show j ≠ g from fun he => ha (he ▸ hj))
      simp only [without,List.filter_cons,equal,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
      change charge X g+((without I g).map (charge X)).sum=_
      rw [he,List.map_cons,List.sum_cons]
    · have hag : a ≠ g := fun he => ha (he ▸ hg)
      have hh := ih hn hg
      simp only [without,List.filter_cons,equal,decide_eq_false hag,Bool.not_false,↓reduceIte,
        List.map_cons,List.sum_cons]
      change charge X g+(charge X a+((without I g).map (charge X)).sum)=_
      omega

end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
structure Invariant {X : Env α} {C : LayerCollection V G} (h : Model X C) (s : State α) : Prop where
  todo : s.1.Sublist (gs X)
  good : GoodPlan h s.2
  upward : ∀ g ∈ s.1, ∀ j ∈ gs X, per X g < per X j → j ∈ s.1
  targets : ∀ r ∈ s.2.2.2, owner X r.target ∈ s.1
  sources : ∀ r ∈ s.2.2.2, r.source ∉ s.1
  distinct : SourcesDistinct s.2.2.2
  ready : ∀ i : C.Id, h.group i.1 ∈ s.1 ∨ Covered X s.2 (h.encode i)

def budget (X : Env α) (s : State α) := planBudget X s.2+(s.1.map (charge X)).sum

omit [Inhabited α] [LinearOrder α] in
theorem length_one_same {δ : Type} {L : List δ} (hh : L.length ≤ 1) {a b : δ} (ha : a ∈ L) (hb : b ∈ L) : a=b := by
  cases L with
  | nil => cases ha
  | cons c L =>
    have he : L=[] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hh; omega
    subst L
    exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm

namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem advance_spec (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (s : State α) (hs : Invariant h s) (hn : s.1 ≠ []) :
    Invariant h (advance vs X M s) ∧ budget X (advance vs X M s) ≤ budget X s ∧
      (advance vs X M s).1.length < s.1.length := by
  let j := pick X s.1
  have hj := (pick_spec X s.1 hn).1
  obtain ⟨g,hg⟩ := (h.groups j).mp (hs.todo.subset hj)
  let R := inRequests X j s.2.2.2
  let T := restRequests X j s.2.2.2
  let o := process vs X j M R
  have hr : ∀ r ∈ R, ValidRequest h r := fun r hr => hs.good.2.2 r ((mem_inRequests ..).mp hr).1
  have htar : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩ := by
    intro r hr'
    obtain ⟨w⟩ := hr r hr'
    have he : h.group w.target.1 = h.group g := by
      rw [← h.owner_eq w.target,w.target_eq,hg]
      exact ((mem_inRequests ..).mp hr').2
    have heg := h.group_inj he
    cases hwt : w.target with
    | mk d i =>
      have hdg : d=g := by simpa only [hwt] using heg
      subst d
      exact ⟨i,by rw [← w.target_eq,hwt]⟩
  have hd : SourcesDistinct R := fun r hr s hs' he => hs.distinct r ((mem_inRequests ..).mp hr).1 s ((mem_inRequests ..).mp hs').1 he
  have hh := h.process_spec vs closed supply M len g R hr htar hd
  rw [hg] at hh
  change GoodPlan h o ∧ _ at hh
  obtain ⟨ho,hcost,hcover,hfulfilled,hsource,hsmall⟩ := hh
  let t : State α := (without s.1 j,join s.2.1 o.1,s.2.2.1++o.2.1,T++o.2.2)
  have he : advance vs X M s = t := by simp only [advance,List.isEmpty_iff,hn,↓reduceIte,t,j,R,T,o]
  rw [he]
  have hmemold : ∀ w ∈ s.2.1, w ∈ t.2.1 := fun w hw => (mem_join hs.good.1.2.2 ho.1.2.1).mpr (Or.inl hw)
  have hmemnew : ∀ w ∈ o.1, w ∈ t.2.1 := fun w hw => (mem_join hs.good.1.2.2 ho.1.2.1).mpr (Or.inr hw)
  have hcovnew (i : ℕ) (hi : Covered X o i) : Covered X t.2 i := by
    rcases hi with hv|⟨b,hb,hi⟩|⟨r,hr,hi⟩
    · exact Or.inl (fun w hw => hmemnew w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_append_right _ hb,hi⟩)
    · exact Or.inr (Or.inr ⟨r,List.mem_append_right _ hr,hi⟩)
  have hcovold (i : ℕ) (hi : Covered X s.2 i) : Covered X t.2 i := by
    rcases hi with hv|⟨b,hb,hi⟩|⟨r,hr,hi⟩
    · exact Or.inl (fun w hw => hmemold w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_append_left _ hb,hi⟩)
    · by_cases ht : owner X r.target=j
      · exact Or.inl (fun w hw => hmemnew w (hfulfilled r ((mem_inRequests ..).mpr ⟨hr,ht⟩) i hi w hw))
      · exact Or.inr (Or.inr ⟨r,List.mem_append_left _ ((mem_restRequests ..).mpr ⟨hr,ht⟩),hi⟩)
  have hnewtarget (r : Request) (hr : r ∈ o.2.2) : owner X r.target ∈ without s.1 j := by
    obtain ⟨w⟩ := ho.2.2 r hr
    have hl := w.later
    rw [hsource r hr] at hl
    have ht : owner X r.target ∈ gs X := by
      rw [← w.target_eq,h.owner_eq]
      exact (h.groups _).mpr ⟨w.target.1,rfl⟩
    exact (mem_without ..).mpr ⟨hs.upward j hj _ ht hl,fun he => (lt_irrefl _ (he ▸ hl))⟩
  refine ⟨?_,?_,without_lt s.1 j hj⟩
  · refine ⟨(List.filter_sublist).trans hs.todo,?_,?_,?_,?_,?_,?_⟩
    · refine ⟨runs_join hs.good.1 ho.1,?_,?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb|hb
        · exact hs.good.2.1 b hb
        · exact ho.2.1 b hb
      · intro r hr
        rcases List.mem_append.mp hr with hr|hr
        · exact hs.good.2.2 r ((mem_restRequests ..).mp hr).1
        · exact ho.2.2 r hr
    · intro a ha b hb hab
      obtain ⟨ha,haj⟩ := (mem_without ..).mp ha
      refine (mem_without ..).mpr ⟨hs.upward a ha b hb hab,?_⟩
      intro he
      subst b
      have hh := (pick_spec X s.1 hn).2 a ha
      change per X j ≤ per X a at hh
      omega
    · intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · obtain ⟨hr,ht⟩ := (mem_restRequests ..).mp hr
        exact (mem_without ..).mpr ⟨hs.targets r hr,ht⟩
      · exact hnewtarget r hr
    · intro r hr hh
      rcases List.mem_append.mp hr with hr|hr
      · exact hs.sources r ((mem_restRequests ..).mp hr).1 ((mem_without ..).mp hh).1
      · exact ((mem_without ..).mp hh).2 (hsource r hr)
    · intro r hr u hu he
      rcases List.mem_append.mp hr with hr|hr <;> rcases List.mem_append.mp hu with hu|hu
      · exact hs.distinct r ((mem_restRequests ..).mp hr).1 u ((mem_restRequests ..).mp hu).1 he
      · exact False.elim (hs.sources r ((mem_restRequests ..).mp hr).1 ((he.trans (hsource u hu)).symm ▸ hj))
      · exact False.elim (hs.sources u ((mem_restRequests ..).mp hu).1 ((he.symm.trans (hsource r hr)).symm ▸ hj))
      · exact length_one_same hsmall hr hu
    · intro i
      rcases hs.ready i with hi|hi
      · by_cases hij : h.group i.1=j
        · have heg : i.1=g := h.group_inj (hij.trans hg.symm)
          obtain ⟨a,k⟩ := i
          change a=g at heg
          subst a
          exact Or.inr (hcovnew _ (hcover k))
        · exact Or.inl ((mem_without ..).mpr ⟨hi,hij⟩)
      · exact Or.inr (hcovold _ hi)
  · have hc := cost_join s.2.1 o.1 [] hs.good.1.2.2 ho.1.2.1
    have hp := sum_partition s.2.2.2 (fun r => equal (owner X r.target) j) (Request.reserve X)
    have hrm := charge_remove X s.1 (h.nodup.sublist hs.todo) j hj
    have hcharge : charge X j = 2*(C.size g*C.period g) := by rw [← hg]; simp only [charge,h.size,h.per_eq]
    simp only [budget,planBudget,t,List.map_append,List.sum_append]
    rw [hc]
    change (R.map (Request.reserve X)).sum+(T.map (Request.reserve X)).sum=(s.2.2.2.map (Request.reserve X)).sum at hp
    unfold planBudget at hcost
    rw [hcharge] at hrm
    dsimp only [o] at hc ⊢
    omega
end Model
end Superstring.CollectionCode

end OAI
