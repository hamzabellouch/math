import OAI.Computability.Superstring.LocalCode

namespace OAI

namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α β : Type}
abbrev Block (α : Type) := ((ℕ × ℕ) × (List ℕ × List α)) × ((ℕ × ℕ) × (Walk α × List (Walk α)))
instance [DecidableEq α] : DecidableEq (Block α) := by
  letI : DecidableEq ((ℕ × ℕ) × (List ℕ × List α)) := inferInstance
  letI : DecidableEq ((ℕ × ℕ) × (Walk α × List (Walk α))) := inferInstance
  exact instDecidableEqProd
instance [Coded α] : Coded (Block α) := by
  letI : Coded ((ℕ × ℕ) × (List ℕ × List α)) := inferInstance
  letI : Coded ((ℕ × ℕ) × (Walk α × List (Walk α))) := inferInstance
  exact codedProd
namespace Block
abbrev source (b : Block α) := b.1.1.1
abbrev target (b : Block α) := b.1.1.2
abbrev members (b : Block α) := b.1.2.1
abbrev word (b : Block α) := b.1.2.2
abbrev period (b : Block α) := b.2.1.1
abbrev reserve (b : Block α) := b.2.1.2
abbrev internal (b : Block α) := b.2.2.1
abbrev links (b : Block α) := b.2.2.2
end Block
abbrev Action (α : Type) := List (Block α) × Walk α

def Covers (L : ℕ → List (List α)) (I : List ℕ) (P : Walk α) : Prop :=
  ∀ i ∈ I, ∀ w ∈ L i, w ∈ P

def Good (V : Set (List α)) (L : ℕ → List (List α)) (P : Walk α) (a : Action α) : Prop :=
  Runs V [] [] a.2 ∧ cost a.2 ≤ cost P+(a.1.map Block.reserve).sum ∧
    (∀ w ∈ P, w ∈ a.2) ∧ ∀ b ∈ a.1, Covers L b.members a.2

structure ValidBlock [LinearOrder β] (V : Set (List α)) (ids : List ℕ)
    (L : ℕ → List (List α)) (owner per : ℕ → ℕ) (rank : ℕ → β) (b : Block α) : Prop where
  period_eq : b.period = per b.source
  target_mem : b.target ∈ ids
  same : ∀ i ∈ b.members, owner i = b.source
  word_mem : b.word ∈ L b.target
  same_short : owner b.target = b.source → b.word.length ≤ b.period
  internal : ∃ s, Runs V s s b.internal ∧ cost b.internal+b.period ≤ b.reserve ∧ Covers L b.members b.internal
  link : ∃ Q ∈ b.links, ∃ s, Runs V s s Q ∧ cost Q ≤ b.reserve ∧ Covers L b.members Q ∧ b.word ∈ Q
  short : rank (owner b.target) ≤ rank b.source →
    ∃ Q ∈ b.links, ∃ s, Runs V s s Q ∧ cost Q ≤ b.reserve ∧ Covers L b.members Q ∧ b.word ∈ Q ∧
      ∃ w ∈ Q, w.length ≤ per (owner b.target)

variable [DecidableEq α]
def singles (P : Walk α) (b : Block α) : List (Action α) :=
  ([b],join P (rootShort b.internal b.period)) :: b.links.map (fun Q => ([b],splice P Q))
def doubles (P : Walk α) (b c : Block α) : List (Action α) :=
  b.links.map (fun Q => ([b,c],join P (rootShort (splice Q c.internal) c.period)))
def pool (P : Walk α) (B : List (Block α)) : List (Action α) :=
  B.flatMap (fun b => singles P b ++ (B.filter (fun c => !(equal c b))).flatMap (doubles P b))

omit [DecidableEq α] in
theorem covers_mono {L : ℕ → List (List α)} {I : List ℕ} {P Q : Walk α}
    (hc : Covers L I P) (h : ∀ w ∈ P, w ∈ Q) : Covers L I Q := fun i hi w hw => h w (hc i hi w hw)

theorem pool_single (P : Walk α) {B : List (Block α)} {b : Block α} (hb : b ∈ B) :
    ([b],join P (rootShort b.internal b.period)) ∈ pool P B := by
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_append_left _ (List.mem_cons_self ..)⟩
theorem pool_link (P : Walk α) {B : List (Block α)} {b : Block α} (hb : b ∈ B)
    {Q : Walk α} (hq : Q ∈ b.links) : ([b],splice P Q) ∈ pool P B := by
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨Q,hq,rfl⟩))⟩
theorem pool_double (P : Walk α) {B : List (Block α)} {b c : Block α} (hb : b ∈ B) (hc : c ∈ B)
    (hne : c ≠ b) {Q : Walk α} (hq : Q ∈ b.links) :
    ([b,c],join P (rootShort (splice Q c.internal) c.period)) ∈ pool P B := by
  apply List.mem_flatMap.mpr
  refine ⟨b,hb,List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,?_,List.mem_map.mpr ⟨Q,hq,rfl⟩⟩)⟩
  simpa only [List.mem_filter,Bool.not_eq_true',equal,decide_eq_false_iff_not] using And.intro hc hne

theorem pool_sane (P : Walk α) (B : List (Block α)) {a : Action α} (ha : a ∈ pool P B) :
    a.1 ≠ [] ∧ a.1.Nodup ∧ ∀ b ∈ a.1, b ∈ B := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨by simp,by simp,by intro c hc; simpa only [List.mem_singleton.mp hc] using hb⟩
    · obtain ⟨Q,_,rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp,by simp,by intro c hc; simpa only [List.mem_singleton.mp hc] using hb⟩
  · obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
    have hc' : c ∈ B ∧ c ≠ b := by
      simpa only [List.mem_filter,Bool.not_eq_true',equal,decide_eq_false_iff_not] using hc
    obtain ⟨Q,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨by simp,by simp [Ne.symm hc'.2],by
      intro d hd; rcases List.mem_cons.mp hd with rfl|hd
      · exact hb
      · exact List.mem_singleton.mp hd ▸ hc'.1⟩

variable [LinearOrder β]
theorem pool_complete {V : Set (List α)} (closed : SubstringClosed V)
    (ids : List ℕ) (L : ℕ → List (List α)) (owner per : ℕ → ℕ) (rank : ℕ → β)
    (P : Walk α) (B : List (Block α)) (hP : Runs V [] [] P) (hne : B ≠ [])
    (valid : ∀ b ∈ B, ValidBlock V ids L owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ L i, w ∈ P) ∨ ∃ b ∈ B, i ∈ b.members) :
    ∃ a ∈ pool P B, Good V L P a := by
  classical
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image B.toFinset (fun b => rank b.source)
    (by obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil B hne; exact ⟨b,List.mem_toFinset.mpr hb⟩)
  have hb : b ∈ B := List.mem_toFinset.mp hb
  have vb := valid b hb
  rcases ready b.target vb.target_mem with hroot | ⟨c,hc,ht⟩
  · obtain ⟨Q,hq,s,hQ,hQc,hcov,hw⟩ := vb.link
    obtain ⟨hS,hSc,hSv⟩ := splice_spec hP hQ ⟨b.word,hroot _ vb.word_mem,hw⟩
    refine ⟨_,pool_link P hb hq,hS,?_,?_,?_⟩
    · simpa only [List.map_singleton,List.sum_singleton,hSc] using Nat.add_le_add_left hQc (cost P)
    · intro w hw; exact (hSv w).mpr (Or.inl hw)
    · intro d hd; have he := List.mem_singleton.mp hd; subst d
      exact covers_mono hcov (fun w hw => (hSv w).mpr (Or.inr hw))
  · by_cases hown : b.target ∈ b.members
    · obtain ⟨s,hI,hIc,hcover⟩ := vb.internal
      obtain ⟨hR,hRc,hRv⟩ := rootShort_spec closed hI b.period
        ⟨b.word,hcover _ hown _ vb.word_mem,vb.same_short (vb.same _ hown)⟩
      have hJ := runs_join hP hR
      have hJc := cost_join P _ _ hP.2.2 hR.2.1
      have hJv (w : List α) := mem_join (w:=w) hP.2.2 hR.2.1
      refine ⟨_,pool_single P hb,hJ,?_,?_,?_⟩
      · simp only [List.map_singleton,List.sum_singleton]; omega
      · intro w hw; exact (hJv w).mpr (Or.inl hw)
      · intro d hd; have he := List.mem_singleton.mp hd; subst d
        exact covers_mono hcover (fun w hw => (hJv w).mpr (Or.inr (hRv w hw)))
    · have hcb : c ≠ b := by intro he; subst c; exact hown ht
      have vc := valid c hc
      have ho := vc.same _ ht
      have hrank : rank (owner b.target) ≤ rank b.source := by
        rw [ho]; exact hmax c (List.mem_toFinset.mpr hc)
      obtain ⟨Q,hq,s,hQ,hQc,hcov,hw,x,hx,hxl⟩ := vb.short hrank
      obtain ⟨t,hI,hIc,hcover⟩ := vc.internal
      obtain ⟨hS,hSc,hSv⟩ := splice_spec hQ hI ⟨b.word,hw,hcover _ ht _ vb.word_mem⟩
      have hlen : x.length ≤ c.period := by simpa only [vc.period_eq,ho] using hxl
      obtain ⟨hR,hRc,hRv⟩ := rootShort_spec closed hS c.period
        ⟨x,(hSv x).mpr (Or.inl hx),hlen⟩
      have hJ := runs_join hP hR
      have hJc := cost_join P _ _ hP.2.2 hR.2.1
      have hJv (w : List α) := mem_join (w:=w) hP.2.2 hR.2.1
      refine ⟨_,pool_double P hb hc hcb hq,hJ,?_,?_,?_⟩
      · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; omega
      · intro w hw; exact (hJv w).mpr (Or.inl hw)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl|hd
        · exact covers_mono hcov (fun w hw => (hJv w).mpr (Or.inr (hRv w ((hSv w).mpr (Or.inl hw)))))
        · have he := List.mem_singleton.mp hd; subst d
          exact covers_mono hcover (fun w hw => (hJv w).mpr (Or.inr (hRv w ((hSv w).mpr (Or.inr hw)))))
end Superstring.BlockClose


namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α : Type} [DecidableEq α] [Inhabited α]

def rootedCheck (vs P : Walk α) : Bool :=
  check vs P && equal (P.take 1) [[]] && equal (P.reverse.take 1) [[]]

theorem rootedCheck_eq (vs P : Walk α) : rootedCheck vs P = true ↔ Runs {w | w ∈ vs} [] [] P := by
  have h (Q : Walk α) : Q.take 1 = [[]] ↔ Q.head? = some [] := by
    cases Q <;> simp
  simp only [rootedCheck,Bool.and_eq_true,check_eq,equal,decide_eq_true_eq,h,List.head?_reverse,Runs]
  tauto

def lookup (L : List (Walk α)) (i : ℕ) : Walk α := L[i]?.getD []
def coversCheck (L : List (Walk α)) (I : List ℕ) (P : Walk α) : Bool :=
  I.all (fun i => (lookup L i).all (fun w => member w P))
omit [Inhabited α] in
theorem coversCheck_eq (L : List (Walk α)) (I : List ℕ) (P : Walk α) :
    coversCheck L I P = true ↔ Covers (lookup L) I P := by
  simp only [coversCheck,List.all_eq_true,member,decide_eq_true_eq,Covers]

def goodCheck (vs : Walk α) (L : List (Walk α)) (P : Walk α) (a : Action α) : Bool :=
  rootedCheck vs a.2 && lessEq (cost a.2) (cost P+(a.1.map Block.reserve).sum) &&
    P.all (fun w => member w a.2) && a.1.all (fun b => coversCheck L b.members a.2)
theorem goodCheck_eq (vs : Walk α) (L : List (Walk α)) (P : Walk α) (a : Action α) :
    goodCheck vs L P a = true ↔ Good {w | w ∈ vs} (lookup L) P a := by
  simp only [goodCheck,Bool.and_eq_true,rootedCheck_eq,lessEq,decide_eq_true_eq,List.all_eq_true,
    member,coversCheck_eq,Good]
  tauto

def select (vs : Walk α) (L : List (Walk α)) (P : Walk α) (B : List (Block α)) : Action α :=
  ((pool P B).filter (goodCheck vs L P)).headD ([],P)
def remaining (B D : List (Block α)) : List (Block α) :=
  B.filter (fun b => !(member b D))

theorem select_spec (vs : Walk α) (L : List (Walk α)) (P : Walk α) (B : List (Block α))
    (hex : ∃ a ∈ pool P B, Good {w | w ∈ vs} (lookup L) P a) :
    select vs L P B ∈ pool P B ∧ Good {w | w ∈ vs} (lookup L) P (select vs L P B) := by
  have hn : (pool P B).filter (goodCheck vs L P) ≠ [] := by
    obtain ⟨a,ha,hg⟩ := hex
    have hm := List.mem_filter.mpr ⟨ha,(goodCheck_eq ..).mpr hg⟩
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  have hm : select vs L P B ∈ (pool P B).filter (goodCheck vs L P) := by
    unfold select
    generalize (pool P B).filter (goodCheck vs L P) = X at hn ⊢
    cases X with
    | nil => exact False.elim (hn rfl)
    | cons a X => exact List.mem_cons_self ..
  have hs := List.mem_filter.mp hm
  exact ⟨hs.1,(goodCheck_eq ..).mp hs.2⟩

omit [Inhabited α] in
theorem mem_remaining (B D : List (Block α)) (b : Block α) :
    b ∈ remaining B D ↔ b ∈ B ∧ b ∉ D := by
  simp only [remaining,List.mem_filter,Bool.not_eq_true',member,decide_eq_false_iff_not]

omit [Inhabited α] in
theorem remaining_budget (B D : List (Block α)) (hd : D.Nodup) (hsub : D ⊆ B) :
    (D.map Block.reserve).sum+((remaining B D).map Block.reserve).sum ≤ (B.map Block.reserve).sum := by
  let E := B.filter (fun b => member b D)
  have hDE : D ⊆ E := fun b hb => List.mem_filter.mpr ⟨hsub hb,(member_eq ..).mpr hb⟩
  obtain ⟨F,hperm,hsub⟩ := hd.subperm hDE
  have hsum := (hsub.map Block.reserve).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [(hperm.map Block.reserve).sum_eq] at hsum
  have hp := ((List.filter_append_perm (fun b => member b D) B).map Block.reserve).sum_eq
  simp only [List.map_append,List.sum_append] at hp
  change (E.map Block.reserve).sum+((remaining B D).map Block.reserve).sum = _ at hp
  omega

omit [Inhabited α] in
theorem remaining_length (B D : List (Block α)) (hne : D ≠ []) (hsub : D ⊆ B) :
    (remaining B D).length < B.length := by
  have hh : (remaining B D).Sublist B := List.filter_sublist
  by_contra hn
  have he : remaining B D = B := hh.eq_of_length (by have := hh.length_le; omega)
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D hne
  have hm : b ∈ remaining B D := by rw [he]; exact hsub hb
  exact ((mem_remaining B D b).mp hm).2 hb

abbrev State (α : Type) := Walk α × List (Block α)
def step (vs : Walk α) (L : List (Walk α)) (s : State α) : State α :=
  let a := select vs L s.1 s.2
  (a.2,remaining s.2 a.1)

variable {β : Type} [LinearOrder β]
theorem step_spec (vs : Walk α) (closed : SubstringClosed {w | w ∈ vs}) (L : List (Walk α))
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β) (s : State α)
    (hP : Runs {w | w ∈ vs} [] [] s.1) (hne : s.2 ≠ [])
    (valid : ∀ b ∈ s.2, ValidBlock {w | w ∈ vs} ids (lookup L) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ s.1) ∨ ∃ b ∈ s.2, i ∈ b.members) :
    Runs {w | w ∈ vs} [] [] (step vs L s).1 ∧
      cost (step vs L s).1+((step vs L s).2.map Block.reserve).sum ≤ cost s.1+(s.2.map Block.reserve).sum ∧
      (∀ w ∈ s.1, w ∈ (step vs L s).1) ∧
      (step vs L s).2.Sublist s.2 ∧ (step vs L s).2.length < s.2.length ∧
      ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ (step vs L s).1) ∨ ∃ b ∈ (step vs L s).2, i ∈ b.members := by
  obtain ⟨ha,hgood⟩ := select_spec vs L s.1 s.2
    (pool_complete closed ids (lookup L) owner per rank s.1 s.2 hP hne valid ready)
  obtain ⟨hn,hd,hsub⟩ := pool_sane s.1 s.2 ha
  obtain ⟨hQ,hQc,hQv,hQb⟩ := hgood
  have hbudget := remaining_budget s.2 (select vs L s.1 s.2).1 hd hsub
  refine ⟨hQ,by dsimp only [step]; omega,hQv,List.filter_sublist,remaining_length _ _ hn hsub,?_⟩
  intro i hi
  rcases ready i hi with h | ⟨b,hb,hm⟩
  · exact Or.inl (fun w hw => hQv w (h w hw))
  · by_cases hd : b ∈ (select vs L s.1 s.2).1
    · exact Or.inl (hQb b hd i hm)
    · exact Or.inr ⟨b,(mem_remaining _ _ _).mpr ⟨hb,hd⟩,hm⟩
end Superstring.BlockClose


namespace Superstring.BitCode.Poly
@[fun_prop] theorem flatMapFn {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : γ × α → List β} {xs : γ → List α} (hf : Poly f) (hxs : Poly xs) :
    Poly (fun c => (xs c).flatMap (fun a => f (c,a))) := by
  simpa only [List.flatMap, Function.comp_def] using flatten.comp (mapFn hf hxs)
end Superstring.BitCode.Poly
namespace Superstring.BlockClose
open BitCode WalkCode
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]
instance codedState : Coded (State α) := codedProd
instance codedAction : Coded (Action α) := codedProd
instance codedContextState : Coded ((Walk α × List (Walk α)) × State α) := codedProd
instance codedContextAction : Coded ((Walk α × List (Walk α)) × (Walk α × Action α)) := codedProd
omit [Inhabited α] in
@[fun_prop] theorem poly_singles : Poly (fun q : Walk α × Block α => singles q.1 q.2) := by
  unfold singles
  have hm : Poly (fun q : Walk α × Block α => q.2.links.map (fun Q => ([q.2],splice q.1 Q))) := by
    apply BitCode.Poly.mapFn (f := fun q : (Walk α × Block α) × Walk α => ([q.1.2],splice q.1.1 q.2))
    · fun_prop
    · fun_prop
  fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_doubles : Poly (fun q : Walk α × Block α × Block α => doubles q.1 q.2.1 q.2.2) := by
  unfold doubles
  apply BitCode.Poly.mapFn (f := fun q : (Walk α × Block α × Block α) × Walk α =>
    ([q.1.2.1,q.1.2.2],join q.1.1 (rootShort (splice q.2 q.1.2.2.internal) q.1.2.2.period)))
  · fun_prop
  · fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_pool : Poly (fun q : Walk α × List (Block α) => pool q.1 q.2) := by
  unfold pool
  apply BitCode.Poly.flatMapFn (f := fun q : (Walk α × List (Block α)) × Block α =>
    singles q.1.1 q.2 ++ (q.1.2.filter (fun c => !(equal c q.2))).flatMap (doubles q.1.1 q.2))
  · apply BitCode.Poly.append.comp (f := fun q : (Walk α × List (Block α)) × Block α =>
      (singles q.1.1 q.2, (q.1.2.filter (fun c => !(equal c q.2))).flatMap (doubles q.1.1 q.2)))
    apply BitCode.Poly.pair (by fun_prop)
    apply BitCode.Poly.flatMapFn
      (f := fun q : ((Walk α × List (Block α)) × Block α) × Block α => doubles q.1.1.1 q.1.2 q.2)
    · fun_prop
    · exact BitCode.Poly.filterFn
        (p := fun q : ((Walk α × List (Block α)) × Block α) × Block α => !(equal q.2 q.1.2))
        (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_rootedCheck : Poly (fun q : Walk α × Walk α => rootedCheck q.1 q.2) := by
  unfold rootedCheck
  fun_prop
omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : List (Walk α) × ℕ => lookup q.1 q.2) := by
  exact BitCode.Poly.getD []
omit [Inhabited α] in
@[fun_prop] theorem poly_coversCheck : Poly (fun q : List (Walk α) × List ℕ × Walk α => coversCheck q.1 q.2.1 q.2.2) := by
  unfold coversCheck
  apply BitCode.Poly.allFn
    (p := fun q : (List (Walk α) × List ℕ × Walk α) × ℕ => (lookup q.1.1 q.2).all (fun w => member w q.1.2.2))
  · exact BitCode.Poly.allFn
      (p := fun q : ((List (Walk α) × List ℕ × Walk α) × ℕ) × List α => member q.2 q.1.1.2.2)
      (by fun_prop) (by fun_prop)
  · fun_prop
omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_reserves : Poly (fun B : List (Block α) => (B.map Block.reserve).sum) := by
  apply BitCode.Poly.sum.comp
  exact BitCode.Poly.mapFn (f := fun q : List (Block α) × Block α => q.2.reserve) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_goodCheck : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
    goodCheck q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hp : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) => q.2.1.all (fun w => member w q.2.2.2)) := by
    exact BitCode.Poly.allFn
      (p := fun q : ((Walk α × List (Walk α)) × (Walk α × Action α)) × List α => member q.2 q.1.2.2.2)
      (by fun_prop) (by fun_prop)
  have hb : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      q.2.2.1.all (fun b => coversCheck q.1.2 b.members q.2.2.2)) := by
    exact BitCode.Poly.allFn
      (p := fun q : ((Walk α × List (Walk α)) × (Walk α × Action α)) × Block α =>
        coversCheck q.1.1.2 q.2.members q.1.2.2.2) (by fun_prop) (by fun_prop)
  have hs : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      (q.2.2.1.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  have hc : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      lessEq (cost q.2.2.2) (cost q.2.1+(q.2.2.1.map Block.reserve).sum)) := by fun_prop
  unfold goodCheck
  fun_prop
omit [DecidableEq α] [Inhabited α] in
theorem poly_shuffle : Poly (fun q : ((Walk α × List (Walk α)) × State α) × Action α =>
    (q.1.1,(q.1.2.1,q.2))) := by
  exact ((BitCode.Poly.fst.comp BitCode.Poly.fst).pair
    ((BitCode.Poly.fst.comp (BitCode.Poly.snd.comp BitCode.Poly.fst)).pair BitCode.Poly.snd))
theorem poly_goodCheck_context : Poly (fun q : ((Walk α × List (Walk α)) × State α) × Action α =>
    goodCheck q.1.1.1 q.1.1.2 q.1.2.1 q.2) := by
  exact BitCode.Poly.comp
    (f := fun q : ((Walk α × List (Walk α)) × State α) × Action α => (q.1.1,(q.1.2.1,q.2)))
    (g := fun q : (Walk α × List (Walk α)) × (Walk α × Action α) => goodCheck q.1.1 q.1.2 q.2.1 q.2.2)
    (poly_goodCheck (α := α)) (poly_shuffle (α := α))
theorem poly_filteredPool : Poly (fun q : (Walk α × List (Walk α)) × State α =>
    (pool q.2.1 q.2.2).filter (goodCheck q.1.1 q.1.2 q.2.1)) := by
  exact BitCode.Poly.filterFn poly_goodCheck_context (poly_pool.comp BitCode.Poly.snd)
@[fun_prop] theorem poly_select : Poly (fun q : (Walk α × List (Walk α)) × State α => select q.1.1 q.1.2 q.2.1 q.2.2) := by
  exact BitCode.Poly.headDWith.comp (poly_filteredPool.pair
    ((BitCode.Poly.const []).pair (BitCode.Poly.fst.comp BitCode.Poly.snd)))
omit [Inhabited α] in
@[fun_prop] theorem poly_remaining : Poly (fun q : List (Block α) × List (Block α) => remaining q.1 q.2) := by
  unfold remaining
  exact BitCode.Poly.filterFn
    (p := fun q : (List (Block α) × List (Block α)) × Block α => !(member q.2 q.1.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_step : Poly (fun q : (Walk α × List (Walk α)) × State α => step q.1.1 q.1.2 q.2) := by
  unfold step
  dsimp only
  fun_prop
end Superstring.BlockClose


namespace Superstring.BlockFactory
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]

def pack (D : GroupData α) (src tar off : ℕ) (js : List ℕ) (a b : ℤ)
    (P : Walk α) (Qs : List (Walk α)) : BlockClose.Block α :=
  (((src,tar),(js.map (off+·),PeriodWord.window D.1 a b)),
    ((D.1.length,2*(js.length*D.1.length)),(P,Qs)))
def individual (D : GroupData α) (src tar off i : ℕ) (a b : ℤ) : BlockClose.Block α :=
  pack D src tar off [i] a b (turn D.1 (exits D i)) [LayerArray.individual D i a b]
def collective (D : GroupData α) (src tar off : ℕ) (js : List ℕ) (lo hi : ℕ) (a b t : ℤ) : BlockClose.Block α :=
  pack D src tar off js a b (band D js lo hi (js.length-1) t)
    [LayerArray.collective D js hi a b,shortSweep D js hi a b t]

omit [DecidableEq α] in
theorem pack_cover {V : Set (List α)} {A : ℤ → α} {p : ℕ} (L : ℕ → Layer V A p)
    {D : GroupData α} {src tar off : ℕ} {js : List ℕ} {a b : ℤ}
    {P Q : Walk α} {Qs : List (Walk α)} {ls : ℕ → Walk α}
    (he : ∀ j ∈ js, ∀ w ∈ ls (off+j), w ∈ (L j).Content)
    (hv : ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ Q) :
    Covers ls (pack D src tar off js a b P Qs).members Q := by
  intro i hi w hw
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact hv j hj w (he j hj w hw)

variable [LinearOrder α]
theorem individual_valid {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {i src tar off : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : (L i).first R.start ≤ R.stop) (hl : R.stop ≤ (L i).last R.start+p)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hself : owner tar = src → p = q)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    ValidBlock V ids ls owner periods rank (individual D src tar off i R.start R.stop) := by
  have hlen := R.length_lt hp hq perA perB hne
  obtain ⟨hI,hIc,hIv⟩ := turn_spec h closed hp perA
  obtain ⟨hQ,hQc,hQv,hR,w,hw,hs⟩ := LayerArray.individual_spec L h closed hp perA letters q
    R.start_le_stop R.word_mem hf hl hlen
  have hword : (individual D src tar off i R.start R.stop).word = textWord A R.start R.stop := by
    simp only [individual,pack,BlockClose.Block.word,PeriodWord.window_eq,h.text_eq]
  have hcov : ∀ P : Walk α, (∀ w ∈ (L i).Content, w ∈ P) →
      Covers ls (individual D src tar off i R.start R.stop).members P := by
    intro P hv j hj w hw
    have he : j = off+i := by simpa only [individual,pack,BlockClose.Block.members,List.map_singleton,List.mem_singleton] using hj
    subst j
    exact hv w (hlayers w hw)
  refine ⟨?_,htar,?_,by rw [hword]; exact hrec,?_,?_,?_,?_⟩
  · change D.1.length = periods src
    exact h.length_eq.trans hsrc.symm
  · intro j hj
    have he : j = off+i := by simpa only [individual,pack,BlockClose.Block.members,List.map_singleton,List.mem_singleton] using hj
    exact he ▸ hown
  · intro he
    have hlen' := R.same_period_length_lt hp perA (by rw [hself he]; exact perB) hne
    change (PeriodWord.window D.1 R.start R.stop).length ≤ D.1.length
    rw [PeriodWord.window_eq,h.text_eq,h.length_eq,length_textWord]
    have := R.start_le_stop; omega
  · refine ⟨_,hI,?_,hcov _ hIv⟩
    change cost (turn D.1 (exits D i))+D.1.length ≤ 2*([i].length*D.1.length)
    simp only [List.length_singleton,one_mul,h.length_eq,hIc]; omega
  · refine ⟨_,List.mem_singleton_self _,_,hQ,?_,hcov _ hQv,?_⟩
    · change cost (LayerArray.individual D i R.start R.stop) ≤ 2*([i].length*D.1.length)
      simp only [List.length_singleton,one_mul,h.length_eq,hQc]; exact le_rfl
    · rw [hword]; exact hR
  · intro _
    refine ⟨_,List.mem_singleton_self _,_,hQ,?_,hcov _ hQv,?_,w,hw,?_⟩
    · change cost (LayerArray.individual D i R.start R.stop) ≤ 2*([i].length*D.1.length)
      simp only [List.length_singleton,one_mul,h.length_eq,hQc]; exact le_rfl
    · rw [hword]; exact hR
    · change w.length ≤ periods (owner tar)
      rw [htper]; exact hs

theorem collective_valid {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {js : List ℕ} {lo hi src tar off : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (hq : 0 < q)
    (perA : Function.Periodic A (p : ℤ)) (perB : Function.Periodic B (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (t : ℤ) (hat : R.start ≤ t) (htb : t < R.stop)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hH : (L hi).first t ≤ R.stop+(js.length*p : ℕ))
    (hgap : (L hi).first R.start-(L lo).last R.start ≤ (js.length*p : ℕ))
    (hB : R.stop ≤ (L lo).last R.start+(js.length*p : ℕ))
    (hsharp : (L hi).first t-(L lo).last t ≤ ((js.length-1)*p : ℕ))
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ j ∈ js, owner (off+j) = src)
    (htper : periods (owner tar) = q) (hself : owner tar = src → p = q)
    (hrank : rank (owner tar) ≤ rank src → ∀ x, forward (fun x => B (x+R.offset)) x ≤ forward A t)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ j ∈ js, ∀ w ∈ ls (off+j), w ∈ (L j).Content) :
    ValidBlock V ids ls owner periods rank (collective D src tar off js lo hi R.start R.stop t) := by
  have hD := h hi hhi
  have hk : 1 ≤ js.length := by have := List.length_pos_of_mem hhi; omega
  obtain ⟨hI,hIc,hIv⟩ := band_spec L h hlo hhi lower upper closed hp perA letters t hsharp
  obtain ⟨hQ,hQc,hQv,hR⟩ := collective_spec L h hlo hhi lower upper closed hp perA letters
    R.start_le_stop R.word_mem ((L hi).first_mono hat |>.trans hH) hgap hB
  have hword : (collective D src tar off js lo hi R.start R.stop t).word = textWord A R.start R.stop := by
    simp only [collective,pack,BlockClose.Block.word,PeriodWord.window_eq,hD.text_eq]
  have hcov : ∀ P : Walk α, (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P) →
      Covers ls (collective D src tar off js lo hi R.start R.stop t).members P := by
    intro P hv i hi w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact hv j hj w (hlayers j hj w hw)
  have hreserve : (collective D src tar off js lo hi R.start R.stop t).reserve = 2*(js.length*p) := by
    change 2*(js.length*D.1.length) = _
    rw [hD.length_eq]
  refine ⟨?_,htar,?_,by rw [hword]; exact hrec,?_,?_,?_,?_⟩
  · change D.1.length = periods src
    exact hD.length_eq.trans hsrc.symm
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact hown j hj
  · intro he
    have hlen := R.same_period_length_lt hp perA (by rw [hself he]; exact perB) hne
    change (PeriodWord.window D.1 R.start R.stop).length ≤ D.1.length
    rw [PeriodWord.window_eq,hD.text_eq,hD.length_eq,length_textWord]
    have := R.start_le_stop; omega
  · refine ⟨_,hI,?_,hcov _ hIv⟩
    rw [hreserve]
    change cost (band D js lo hi (js.length-1) t)+D.1.length ≤ _
    rw [hD.length_eq]
    have he : (js.length-1+js.length)*p+p = 2*(js.length*p) := by
      have : js.length-1+1 = js.length := by omega
      calc (js.length-1+js.length)*p+p = (js.length-1+1+js.length)*p := by ring
           _ = 2*(js.length*p) := by rw [this]; ring
    omega
  · refine ⟨_,List.mem_cons_self ..,_,hQ,?_,hcov _ hQv,?_⟩
    · rw [hreserve]; exact hQc.le
    · rw [hword]; exact hR
  · intro hr
    have perB' : Function.Periodic (fun x => B (x+R.offset)) (q : ℤ) := by
      intro x
      simpa only [add_right_comm] using perB (x+R.offset)
    obtain ⟨P,hmem,hP,hPc,hPv,hPr,w,hw,hwlen⟩ := collective_contact L h hlo hhi lower upper
      closed hp perA letters q hq perB' hat htb R.word_mem R.agree hne hmax (hrank hr) hH hgap hB
    refine ⟨P,hmem,_,hP,?_,hcov _ hPv,?_,w,hw,?_⟩
    · rw [hreserve]; exact hPc.le
    · rw [hword]; exact hPr
    · change w.length ≤ periods (owner tar)
      rw [htper]; exact hwlen

end Superstring.BlockFactory

end OAI
