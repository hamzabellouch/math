import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.WordComponents

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

def Survives (S : Schedule q) (d : ℕ) (w : List (Cell q)) : Prop :=
  ∀ p z s, Reach S d w (p ++ z ++ s) → ¬ Zero S d z

lemma Survives.of_reach {v w : List (Cell q)} (hv : Survives S d v)
    (h : Reach S d v w) : Survives S d w := by
  intro p z s hz
  exact hv p z s (h.trans hz)

lemma Survives.infix {v w : List (Cell q)} (hw : Survives S d w)
    (hi : v <:+: w) : Survives S d v := by
  obtain ⟨a,b,rfl⟩ := hi
  intro p z s hr hz
  have hh := reach_context hr a b
  apply hw (a++p) z (s++b) _ hz
  simpa only [List.append_assoc] using hh

lemma Survives.not_zero {w : List (Cell q)} (hw : Survives S d w) : ¬ Zero S d w := by
  exact hw [] w [] (by simpa using (Relation.ReflTransGen.refl : Reach S d w w))

lemma Survives.format {w : List (Cell q)} (hw : Survives S d w) {a : Cell q}
    (ha : a ∈ w) : a.Format S d := by
  obtain ⟨p,s,rfl⟩ := List.append_of_mem ha
  by_contra h
  exact hw p [a] s (by simpa using (Relation.ReflTransGen.refl : Reach S d (p ++ a :: s) (p ++ a :: s))) (Or.inl ⟨a,rfl,Or.inl h⟩)

lemma Survives.pair {w : List (Cell q)} (hw : Survives S d w) {a b : Cell q}
    (hab : [a,b] <:+: w) : Pair a b := by
  by_contra h
  exact (hw.infix hab).not_zero (Or.inr ⟨a,b,rfl,Or.inl h⟩)

lemma Survives.chain {w : List (Cell q)} (hw : Survives S d w) : w.IsChain Pair := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      apply List.isChain_cons_cons.mpr
      constructor
      · exact hw.pair ⟨[],w,by simp⟩
      · exact ih (hw.infix ⟨[a],[],by simp⟩)

namespace Cell

def transactionRank (c : Cell q) : ℕ := match c.marker with
  | .left => 0 | .boundary | .full => 1 | .right => 2 | .idle => 3

def checkerRank (c : Cell q) : ℕ := match c.checker with
  | .passed _ => 0 | .head _ => 1 | .idle => 2

def paletteRank (c : Cell q) : ℕ := c.transactionRank + c.checkerRank

omit [NeZero q] in
lemma paletteRank_lt (c : Cell q) : c.paletteRank < 6 := by
  unfold paletteRank transactionRank checkerRank
  cases c.marker <;> cases c.checker <;> simp

def eraseColor (c : Cell q) : Cell q := c.setColor 0

def color (c : Cell q) : Fin q := match c.pos with
  | .palette x => x | _ => 0

omit [NeZero q] in
@[simp] lemma setColor_setColor (c : Cell q) (x y : Fin q) :
    (c.setColor x).setColor y = c.setColor y := by
  cases c; rfl

omit [NeZero q] in
@[simp] lemma setColor_of_palette (c : Cell q) {x : Fin q} (h : c.pos = .palette x) :
    c.setColor x = c := by
  cases c with | mk sk ch dat cert head => cases sk; simp_all [pos,setColor]

lemma recoverColor (c : Cell q) (hc : c.isPalette) :
    c.eraseColor.setColor c.color = c := by
  obtain ⟨x,hx⟩ := hc
  simp only [eraseColor, setColor_setColor, color, hx]
  exact c.setColor_of_palette hx

lemma not_first_of_palette (c : Cell q) (hc : c.isPalette) : ¬c.skeleton.first := by
  obtain ⟨x,hx⟩ := hc
  change c.skeleton.pos = .palette x at hx
  simp [Skeleton.first, hx]

omit [NeZero q] in
lemma not_last_of_palette (c : Cell q) (hc : c.isPalette) : ¬c.skeleton.last := by
  obtain ⟨x,hx⟩ := hc
  change c.skeleton.pos = .palette x at hx
  simp [Skeleton.last, hx]
end Cell

lemma palette_marker_pair {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) :
    (a.marker = .idle ∧ b.marker = .idle) ∨
    (a.marker = .left ∧ (b.marker = .left ∨ b.marker = .boundary ∨ b.marker = .full)) ∨
    (a.marker = .boundary ∧ b.marker = .idle) ∨
    (a.marker = .full ∧ b.marker = .right) ∨
    (a.marker = .right ∧ b.marker = .right) := by
  have haf := a.not_first_of_palette ha
  have hal := a.not_last_of_palette ha
  have hbf := b.not_first_of_palette hb
  have hbl := b.not_last_of_palette hb
  have hh := hp.1.2
  simp only [Skeleton.rightExternal, Skeleton.leftExternal, Skeleton.acceptsRight,
    Skeleton.acceptsLeft, hal, hbf, and_false, or_false] at hh
  cases hma : a.marker <;> cases hmb : b.marker <;>
    simp_all only [Cell.marker, reduceCtorEq, and_self, or_self,
      or_true, or_false, true_and, and_true, false_and, and_false,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false]

lemma palette_rank_nondecreasing {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) :
    a.transactionRank ≤ b.transactionRank ∧ a.checkerRank ≤ b.checkerRank := by
  constructor
  · have hh := palette_marker_pair ha hb hp
    rcases hh with ⟨h,h'⟩ | ⟨h,hh⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩
    all_goals try {simp [Cell.transactionRank,h,h']}
    rcases hh with h' | h' | h' <;> simp [Cell.transactionRank,h,h']
  · have hh := hp.2.1 ⟨ha,hb⟩
    generalize hca : a.checker = ca at hh
    generalize hcb : b.checker = cb at hh
    cases hh <;> simp [Cell.checkerRank,hca,hcb]

lemma palette_equal_markerRank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) (he : a.transactionRank = b.transactionRank) :
    a.marker = b.marker ∧ (a.marker = .idle ∨ a.marker = .left ∨ a.marker = .right) := by
  have hh := palette_marker_pair ha hb hp
  rcases hh with ⟨h,h'⟩ | ⟨h,h'|h'|h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ <;>
    simp_all [Cell.transactionRank]

omit [NeZero q] in
lemma palette_equal_checkerRank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) (he : a.checkerRank = b.checkerRank) :
    a.checker = b.checker ∧ ∀ x, a.checker ≠ .head x := by
  have hh := hp.2.1 ⟨ha,hb⟩
  generalize hca : a.checker = ca at hh
  generalize hcb : b.checker = cb at hh
  cases hh <;> simp_all [Cell.checkerRank]

omit [NeZero q] in
lemma palette_internal_metadata {a b : Cell q} (ha : a.isPalette)
    (hi : Internal a.skeleton b.skeleton) : a.metadata = b.metadata := by
  obtain ⟨x,hx⟩ := ha
  change a.skeleton.pos = .palette x at hx
  rcases hi with ⟨har,ht,hbl,_,_⟩
  simp only [hx, reduceCtorEq, ite_false] at hbl
  change a.skeleton.metadata = b.skeleton.metadata
  generalize hma : a.skeleton.metadata = ma at har ht hbl ⊢
  generalize hmb : b.skeleton.metadata = mb at har ht hbl ⊢
  cases ma with | mk ar ta bl =>
    cases mb with | mk ar' ta' bl' =>
      simp only at har ht hbl
      subst ar'; subst ta'
      congr 1
      exact Fin.ext hbl

lemma palette_equal_metadata {a b : Cell q} (ha : a.isPalette) (_hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (hp : Pair a b)
    (he : a.marker = b.marker) (hn : a.marker = .idle ∨ a.marker = .left ∨ a.marker = .right) :
    a.metadata = b.metadata := by
  rcases hn with hi | hn
  · exact (hfa.2.2.2.2.1 hi).1.trans ((hfb.2.2.2.2.1 (he ▸ hi)).1.symm)
  · rcases hp.1.2 with hh | hh
    · have hal := a.not_last_of_palette ha
      have hh := hh.1
      rcases hn with hn | hn <;>
        simp_all [Skeleton.rightExternal,Cell.marker]
    · exact palette_internal_metadata ha hh.2.2.2.2

lemma palette_equal_rank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (hp : Pair a b)
    (hr : a.paletteRank = b.paletteRank) :
    a.eraseColor = b.eraseColor ∧ a.HeadFree ∧ b.HeadFree := by
  have hm := palette_rank_nondecreasing ha hb hp
  have htr : a.transactionRank = b.transactionRank := by
    unfold Cell.paletteRank at hr; omega
  have hcr : a.checkerRank = b.checkerRank := by
    unfold Cell.paletteRank at hr; omega
  obtain ⟨hem,hnm⟩ := palette_equal_markerRank ha hb hp htr
  obtain ⟨hec,hnc⟩ := palette_equal_checkerRank ha hb hp hcr
  have hmeta := palette_equal_metadata ha hb hfa hfb hp hem hnm
  have hna : ¬a.isCore := by
    obtain ⟨x,hx⟩ := ha
    rintro ⟨p,hp⟩; rw [hx] at hp; cases hp
  have hnb : ¬b.isCore := by
    obtain ⟨x,hx⟩ := hb
    rintro ⟨p,hp⟩; rw [hx] at hp; cases hp
  obtain ⟨hda,hca⟩ := hfa.2.2.2.1 hna
  obtain ⟨hdb,hcb⟩ := hfb.2.2.2.1 hnb
  have hhead (c : Cell q) (hf : c.Format S d)
      (hn : c.marker = .idle ∨ c.marker = .left ∨ c.marker = .right) :
      c.head = defaultHead := by
    rcases hn with hi | hn
    · exact (hf.2.2.2.2.1 hi).2.1
    · exact hf.2.2.2.2.2.1 hn
  have hha := hhead a hfa hnm
  have hhb := hhead b hfb (hem ▸ hnm)
  have hnon : ¬IsHead a.skeleton := by
    change ¬(a.marker = .boundary ∨ a.marker = .full)
    rcases hnm with h | h | h <;> simp [h]
  have hnon' : ¬IsHead b.skeleton := by
    change ¬(b.marker = .boundary ∨ b.marker = .full)
    change ¬(a.marker = .boundary ∨ a.marker = .full) at hnon
    simpa only [←hem] using hnon
  refine ⟨?_, ⟨hnon,hnc⟩, ⟨hnon',?_⟩⟩
  · cases a with | mk ska cha da ca hea =>
      cases b with | mk skb chb db cb heb =>
        cases ska; cases skb
        simp_all [Cell.eraseColor,Cell.setColor,Cell.marker,Cell.metadata]
  · simpa only [←hec] using hnc

lemma replacement_swap_of_same_fields {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (he : a.eraseColor = b.eraseColor)
    (hf : a.HeadFree) (hf' : b.HeadFree) : Replacement S d [a,b] [b,a] := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  have hset : a.setColor y = b := by
    have hh := congrArg (fun c : Cell q => c.setColor y) he
    simpa only [Cell.eraseColor,Cell.setColor_setColor,b.setColor_of_palette hy] using hh
  refine ⟨?_,Or.inr ⟨a,b,b,a,rfl,rfl,Or.inl (.swap a b x y hx hy hset hf hf')⟩⟩
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro c ((rfl|rfl)|(rfl|rfl)) <;> assumption

lemma Survives.palette_rank_chain {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette) :
    (w.map Cell.paletteRank).IsChain (· ≤ ·) := by
  exact (List.isChain_map Cell.paletteRank).mpr (hw.chain.imp_of_mem_imp (by
    intro a b ha hb hab
    have hh := palette_rank_nondecreasing (hp a ha) (hp b hb) hab
    exact Nat.add_le_add hh.1 hh.2))

lemma Survives.palette_rank_head_le {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w)) (hp : ∀ c ∈ a::w, c.isPalette) (hb : b ∈ w) :
    a.paletteRank ≤ b.paletteRank := by
  have hh := hw.palette_rank_chain hp
  exact hh.rel_cons (List.mem_map_of_mem hb)

lemma Survives.palette_no_collision {a b : Cell q} (p : List (Cell q))
    (hw : Survives S d (a :: p ++ [b]))
    (hp : ∀ c ∈ a :: p ++ [b], c.isPalette)
    (hr : a.paletteRank = b.paletteRank) (hc : a.color = b.color) : False := by
  induction p with
  | nil =>
    obtain ⟨x,hx⟩ := hp a (by simp)
    obtain ⟨y,hy⟩ := hp b (by simp)
    have hxy : x = y := by simpa only [Cell.color,hx,hy] using hc
    subst y
    apply hw.not_zero
    exact Or.inr ⟨a,b,rfl,Or.inr (Or.inl ⟨x,hx,hy⟩)⟩
  | cons c p ih =>
    have hac : a.paletteRank ≤ c.paletteRank :=
      hw.palette_rank_head_le hp (by simp)
    have hwt : Survives S d (c :: p ++ [b]) := hw.infix ⟨[a],[],by simp⟩
    have hpt : ∀ v ∈ c :: p ++ [b], v.isPalette := fun v hv => hp v (List.mem_cons_of_mem a hv)
    have hcb : c.paletteRank ≤ b.paletteRank :=
      hwt.palette_rank_head_le hpt (by simp)
    have hac' : a.paletteRank = c.paletteRank := by omega
    have hab : Pair a c := hw.pair ⟨[],p++[b],by simp⟩
    have ha := hp a (by simp)
    have hcp := hp c (by simp)
    obtain ⟨he,hf,hf'⟩ := palette_equal_rank ha hcp
      (hw.format (by simp)) (hw.format (by simp)) hab hac'
    have hrep := replacement_swap_of_same_fields ha hcp
      (hw.format (by simp)) (hw.format (by simp)) he hf hf'
    have hstep : Step S d (a :: c :: p ++ [b]) (c :: a :: p ++ [b]) :=
      ⟨[],p++[b],[a,c],[c,a],by simp,by simp,hrep⟩
    have hnew := hw.of_reach (Relation.ReflTransGen.single hstep)
    apply ih (hnew.infix ⟨[c],[],by simp⟩)
    intro v hv
    apply hp v
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hv ⊢
    tauto

namespace Cell
def paletteSignature (c : Cell q) : Fin 6 × Fin q :=
  (⟨c.paletteRank,c.paletteRank_lt⟩,c.color)

omit [NeZero q] in
lemma paletteRank_setColor (c : Cell q) (x : Fin q) :
    (c.setColor x).paletteRank = c.paletteRank := rfl

lemma paletteRank_eq_of_eraseColor_eq {a b : Cell q} (he : a.eraseColor = b.eraseColor) :
    a.paletteRank = b.paletteRank := by
  simpa only [eraseColor,paletteRank_setColor] using congrArg paletteRank he
end Cell

lemma Survives.palette_signature_nodup {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette) : (w.map Cell.paletteSignature).Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih (hw.infix ⟨[a],[],by simp⟩)
      (fun c hc => hp c (List.mem_cons_of_mem a hc))⟩
    intro hh
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hh
    obtain ⟨p,s,rfl⟩ := List.append_of_mem hb
    have hs : Survives S d (a :: p ++ [b]) :=
      hw.infix ⟨[],s,by simp [List.append_assoc]⟩
    have hp' : ∀ c ∈ a :: p ++ [b], c.isPalette := by
      intro c hc
      apply hp c
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc ⊢
      tauto
    have hre := congrArg (fun x : Fin 6 × Fin q => x.1.val) he
    have hce := congrArg (fun x : Fin 6 × Fin q => x.2) he
    exact hs.palette_no_collision p hp' hre.symm hce.symm

theorem palette_fragment_bound {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette) : w.length ≤ 16*q+2 := by
  have hh := (hw.palette_signature_nodup hp).length_le_card
  simp only [List.length_map,Fintype.card_prod,Fintype.card_fin] at hh
  omega

theorem eligible_adjacent_swap {a b : Cell q} (hw : Survives S d [a,b])
    (ha : a.isPalette) (hb : b.isPalette) (he : a.eraseColor = b.eraseColor)
    (hfa : a.HeadFree) (hfb : b.HeadFree) : Replacement S d [a,b] [b,a] :=
  replacement_swap_of_same_fields ha hb (hw.format (by simp)) (hw.format (by simp)) he hfa hfb

theorem eligible_run_distinct {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette)
    (he : ∀ a ∈ w, ∀ b ∈ w, a.eraseColor = b.eraseColor) : (w.map Cell.color).Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih (hw.infix ⟨[a],[],by simp⟩)
      (fun c hc => hp c (List.mem_cons_of_mem a hc))
      (fun c hc e he' => he c (List.mem_cons_of_mem a hc) e (List.mem_cons_of_mem a he'))⟩
    intro hh
    obtain ⟨b,hb,hc⟩ := List.mem_map.mp hh
    have hr := Cell.paletteRank_eq_of_eraseColor_eq (he a (by simp) b (by simp [hb]))
    obtain ⟨p,s,rfl⟩ := List.append_of_mem hb
    have hs : Survives S d (a :: p ++ [b]) := hw.infix ⟨[],s,by simp [List.append_assoc]⟩
    apply hs.palette_no_collision p _ hr hc.symm
    intro c hc
    apply hp c
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc ⊢
    tauto

namespace Cell

def Cut (c : Cell q) : Prop :=
  c.pos = .core 0 ∧ (c.marker = .idle ∨ c.metadata.block.val = 0)

def blockRank (c : Cell q) : ℕ := if c.marker = .idle then 10 else c.metadata.block.val

def geometryRank (c : Cell q) : ℕ := (q+2)*c.blockRank + c.positionRank

lemma cut_of_first {c : Cell q} (hf : c.skeleton.first) : c.Cut := by
  rcases hf with ⟨hb,p,hp,hv⟩
  have hp0 : p = 0 := Fin.ext hv
  exact ⟨hp0 ▸ hp,Or.inr hb⟩

omit [NeZero q] in
lemma blockRank_lt (c : Cell q) : c.blockRank < 11 := by
  have h₁ := c.metadata.arity.isLt
  have h₂ := c.metadata.block.isLt
  unfold blockRank
  split_ifs <;> omega

omit [NeZero q] in
lemma blockRank_lt_ten {c : Cell q} (h : c.marker ≠ .idle) : c.blockRank < 10 := by
  have h₁ := c.metadata.arity.isLt
  have h₂ := c.metadata.block.isLt
  simp only [blockRank,ite_eq_right h]
  omega

omit [NeZero q] in
lemma positionRank_lt (c : Cell q) : c.positionRank < q+2 := by
  unfold positionRank
  cases c.pos with
  | core p => have := p.isLt; dsimp only; omega
  | palette a => dsimp only; omega
  | stop => dsimp only; omega

omit [NeZero q] in
lemma geometryRank_lt (c : Cell q) : c.geometryRank < 11*(q+2) := by
  have h₁ := c.blockRank_lt
  have h₂ := c.positionRank_lt
  unfold geometryRank
  nlinarith
end Cell

lemma pair_noCut_external_idle {b : Cell q} (hb : ¬b.Cut)
    (he : b.skeleton.leftExternal) : b.marker = .idle := by
  rcases he with he | ⟨_,he⟩
  · exact he
  · exact (hb (Cell.cut_of_first he)).elim

omit [NeZero q] in
lemma pair_internal_nonidle {a b : Cell q}
    (ha : ¬a.skeleton.rightExternal) (hb : ¬b.skeleton.leftExternal) :
    a.marker ≠ .idle ∧ b.marker ≠ .idle := by
  constructor
  · intro h; exact ha (Or.inl h)
  · intro h; exact hb (Or.inl h)

lemma pair_noCut_blockRank {a b : Cell q} (hp : Pair a b) (hb : ¬b.Cut) :
    a.blockRank ≤ b.blockRank := by
  rcases hp.1.2 with he | hi
  · have hb' := pair_noCut_external_idle hb he.2
    have := a.blockRank_lt
    simp only [Cell.blockRank,hb',ite_eq_left] at *
    omega
  · obtain ⟨ha',hb'⟩ := pair_internal_nonidle hi.1 hi.2.1
    have hbl := hi.2.2.2.2.2.2.1
    simp only [Cell.blockRank,ite_eq_right ha',ite_eq_right hb',Cell.metadata]
    split_ifs at hbl <;> omega

lemma pair_noCut_stop_core {a b : Cell q} {p : Fin q} (hp : Pair a b) (hb : ¬b.Cut)
    (ha : a.pos = .stop) (hpos : b.pos = .core p) : a.blockRank < b.blockRank := by
  have hp0 : p=0 := by
    have hh := hp.1.1
    change a.skeleton.pos = .stop at ha
    change b.skeleton.pos = .core p at hpos
    simp only [Structural,ha,hpos] at hh
    exact Fin.ext hh
  rcases hp.1.2 with he | hi
  · have hb' := pair_noCut_external_idle hb he.2
    exact (hb ⟨hp0 ▸ hpos,Or.inl hb'⟩).elim
  · obtain ⟨ha',hb'⟩ := pair_internal_nonidle hi.1 hi.2.1
    have hbl := hi.2.2.2.2.2.2.1
    change a.skeleton.pos = .stop at ha
    simp only [ha,ite_eq_left] at hbl
    simp only [Cell.blockRank,ite_eq_right ha',ite_eq_right hb',Cell.metadata]
    omega

lemma pair_noCut_geometry {a b : Cell q} (hp : Pair a b) (hb : ¬b.Cut) :
    a.geometryRank ≤ b.geometryRank ∧
      (a.geometryRank = b.geometryRank → a.isPalette ∧ b.isPalette) := by
  have hr := pair_noCut_blockRank hp hb
  have haL := a.positionRank_lt
  have hbL := b.positionRank_lt
  by_cases hlt : a.blockRank < b.blockRank
  · have hh : a.geometryRank < b.geometryRank := by
      unfold Cell.geometryRank; nlinarith
    exact ⟨hh.le,fun he => (Nat.ne_of_lt hh he).elim⟩
  have heq : a.blockRank = b.blockRank := by omega
  have hstr := hp.1.1
  generalize hpa : a.pos = pa
  generalize hpb : b.pos = pb
  change (match a.pos,b.pos with
    | .core p,.core r => p.val+1=r.val
    | .core p,.palette _ => p.val+1=q
    | .palette _,.palette _ => True
    | .palette _,.stop => True
    | .stop,.core r => r.val=0
    | _,_ => False) at hstr
  rw [hpa,hpb] at hstr
  cases pa <;> cases pb <;> simp only at hstr
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · exact ⟨by simp [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq],
      fun _ => ⟨⟨_,hpa⟩,⟨_,hpb⟩⟩⟩
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · have hh := pair_noCut_stop_core hp hb hpa hpb
    omega

lemma Survives.geometry_rank_chain {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ a ∈ w, ¬a.Cut) : (w.map Cell.geometryRank).IsChain (· ≤ ·) := by
  exact (List.isChain_map Cell.geometryRank).mpr (hw.chain.imp_of_mem_imp (by
    intro a b ha hb hab
    exact (pair_noCut_geometry hab (hn b hb)).1))

lemma Survives.geometry_rank_head_le {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w)) (hn : ∀ c ∈ a::w, ¬c.Cut) (hb : b∈w) :
    a.geometryRank ≤ b.geometryRank :=
  (hw.geometry_rank_chain hn).rel_cons (List.mem_map_of_mem hb)

lemma Survives.palette_of_geometry_collision {a b : Cell q} (p : List (Cell q))
    (hw : Survives S d (a::p++[b])) (hn : ∀ c ∈ a::p++[b], ¬c.Cut)
    (hr : a.geometryRank = b.geometryRank) : ∀ c ∈ a::p++[b], c.isPalette := by
  induction p generalizing a with
  | nil =>
    have hp := (pair_noCut_geometry (hw.pair ⟨[],[],by simp⟩) (hn b (by simp))).2 hr
    simpa only [List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using hp
  | cons c p ih =>
    have hac : a.geometryRank ≤ c.geometryRank := hw.geometry_rank_head_le hn (by simp)
    have hwt : Survives S d (c::p++[b]) := hw.infix ⟨[a],[],by simp⟩
    have hnt : ∀ v ∈ c::p++[b], ¬v.Cut := fun v hv => hn v (List.mem_cons_of_mem a hv)
    have hcb : c.geometryRank ≤ b.geometryRank := hwt.geometry_rank_head_le hnt (by simp)
    have hac' : a.geometryRank = c.geometryRank := by omega
    have hcb' : c.geometryRank = b.geometryRank := by omega
    have hp := (pair_noCut_geometry (hw.pair ⟨[],p++[b],by simp⟩) (hn c (by simp))).2 hac'
    have ht := ih (a := c) hwt hnt hcb'
    intro v hv
    change v∈a::(c::p++[b]) at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hp.1
    · exact ht v hv

namespace Cell
abbrev GeometrySignature (q : ℕ) := Fin 11 × ((Fin q) ⊕ ((Fin 6 × Fin q) ⊕ Unit))

def geometrySignature (c : Cell q) : GeometrySignature q :=
  (⟨c.blockRank,c.blockRank_lt⟩,match c.pos with
  | .core p => .inl p
  | .palette _ => .inr (.inl c.paletteSignature)
  | .stop => .inr (.inr ()))

def GeometrySignature.geometry (x : GeometrySignature q) : ℕ :=
  (q+2)*x.1.val + x.2.elim Fin.val (Sum.elim (fun _ => q) (fun _ => q+1))

lemma geometrySignature_geometry (c : Cell q) :
    c.geometrySignature.geometry = c.geometryRank := by
  unfold geometrySignature GeometrySignature.geometry geometryRank positionRank
  cases c.pos <;> rfl

lemma geometryRank_eq_of_signature_eq {a b : Cell q} (he : a.geometrySignature=b.geometrySignature) :
    a.geometryRank=b.geometryRank := by
  simpa only [geometrySignature_geometry] using congrArg GeometrySignature.geometry he

lemma paletteSignature_eq_of_geometrySignature_eq {a b : Cell q}
    (ha : a.isPalette) (hb : b.isPalette) (he : a.geometrySignature=b.geometrySignature) :
    a.paletteSignature=b.paletteSignature := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  have hh := congrArg Prod.snd he
  simpa only [geometrySignature,hx,hy,Sum.inr.injEq,Sum.inl.injEq] using hh
end Cell

lemma Survives.geometry_signature_nodup {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w, ¬c.Cut) : (w.map Cell.geometrySignature).Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih (hw.infix ⟨[a],[],by simp⟩)
      (fun c hc => hn c (List.mem_cons_of_mem a hc))⟩
    intro hh
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hh
    have hr := Cell.geometryRank_eq_of_signature_eq he.symm
    obtain ⟨p,s,rfl⟩ := List.append_of_mem hb
    have hs : Survives S d (a::p++[b]) := hw.infix ⟨[],s,by simp [List.append_assoc]⟩
    have hn' : ∀ c ∈ a::p++[b], ¬c.Cut := by
      intro c hc
      apply hn c
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc ⊢
      tauto
    have hp := hs.palette_of_geometry_collision p hn' hr
    have hpSig := Cell.paletteSignature_eq_of_geometrySignature_eq
      (hp a (by simp)) (hp b (by simp)) he.symm
    have hrr := congrArg (fun x : Fin 6 × Fin q => x.1.val) hpSig
    have hcc := congrArg (fun x : Fin 6 × Fin q => x.2) hpSig
    exact hs.palette_no_collision p hp hrr hcc

lemma Survives.cut_free_length {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w, ¬c.Cut) : w.length ≤ 77*q+11 := by
  have hh := (hw.geometry_signature_nodup hn).length_le_card
  simp only [List.length_map,Cell.GeometrySignature,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_unit] at hh
  calc
    w.length ≤ 11*(q+(6*q+1)) := hh
    _ = 77*q+11 := by ring

theorem cut_free_fragment_bound {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w.tail, ¬c.Cut) : w.length ≤ (10+2)*(17*q+3) := by
  cases w with
  | nil => simp
  | cons a w =>
    have hwt := hw.infix (show w <:+: a::w from ⟨[a],[],by simp⟩)
    have hh := hwt.cut_free_length hn
    simp only [List.length_cons]
    omega

def canonicalCell (bits : Fin d → ZMod 2) (p : Position q) : Cell q :=
  { skeleton := ⟨p,.idle,defaultMeta⟩
    checker := .idle
    data := fun side => if side then 0 else
      match p with
      | .core r => if h : r.val < d then bits ⟨r.val,h⟩ else 0
      | _ => 0
    certificate := 0
    head := defaultHead }

def canonicalBlock (bits : Fin d → ZMod 2) : List (Cell q) :=
  (List.finRange q).map (fun p => canonicalCell bits (.core p)) ++
  (List.finRange q).map (fun x => canonicalCell bits (.palette x)) ++
  [canonicalCell bits .stop]

def encodeWord (w : List (Fin d → ZMod 2)) : List (Cell q) := w.flatMap canonicalBlock

@[simp] lemma canonicalCell_pos (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).pos=p := rfl

@[simp] lemma canonicalCell_marker (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).marker=.idle := rfl

@[simp] lemma canonicalCell_checker (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).checker=.idle := rfl

@[simp] lemma canonicalBlock_length (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).length=2*q+1 := by
  simp [canonicalBlock]; omega

@[simp] lemma encodeWord_length (w : List (Fin d → ZMod 2)) :
    (encodeWord (q:=q) w).length=(2*q+1)*w.length := by
  induction w with
  | nil => simp [encodeWord]
  | cons a w ih =>
    change (canonicalBlock a ++ encodeWord w).length = (2*q+1) * (a::w).length
    rw [List.length_append, canonicalBlock_length, ih, List.length_cons, Nat.mul_succ]
    omega

lemma canonicalCell_format (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).Format S d := by
  cases p with
  | core r =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    intro hd
    funext side
    simp [Nat.not_lt_of_ge hd]
  | palette x =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    rfl
  | stop =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    rfl

lemma canonicalBlock_format (bits : Fin d → ZMod 2) :
    ∀ c ∈ canonicalBlock (q:=q) bits, c.Format S d := by
  intro c hc
  simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
  rcases hc with (⟨p,_,rfl⟩|⟨x,_,rfl⟩)|rfl <;> exact canonicalCell_format _ _

lemma finRange_head : (List.finRange q).head? = some (0 : Fin q) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simpa using NeZero.pos q)]
  simp only [List.getElem_finRange]
  rfl

lemma finRange_last : (List.finRange q).getLast? = some ⟨q-1, Nat.sub_lt (NeZero.pos q) (by decide)⟩ := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_finRange]
  rw [List.getElem?_eq_getElem (by simpa using Nat.sub_lt (NeZero.pos q) (show 0<1 by omega))]
  simp only [List.getElem_finRange]
  rfl

lemma canonicalCell_pair (a b : Fin d → ZMod 2) (p r : Position q)
    (h : Skeleton.Structural (canonicalCell a p).skeleton (canonicalCell b r).skeleton) :
    Pair (canonicalCell a p) (canonicalCell b r) := by
  refine ⟨⟨h,Or.inl ⟨?_,?_⟩⟩, ?_⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · simp [CheckerPair,canonicalCell,Palette.LastOK]

lemma canonicalBlock_pair_chain (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).IsChain Pair := by
  have hc : ((List.finRange q).map (fun p => canonicalCell bits (.core p))).IsChain Pair := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map,List.length_finRange] at hi
    simp only [List.getElem_map,List.getElem_finRange]
    apply canonicalCell_pair bits bits
    rfl
  have hp : ((List.finRange q).map (fun p => canonicalCell bits (.palette p))).IsChain Pair := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_map,List.getElem_finRange]
    apply canonicalCell_pair bits bits
    trivial
  apply (hc.append hp ?_).append (List.isChain_singleton _) ?_
  · intro a ha b hb
    rw [List.getLast?_map,finRange_last] at ha
    rw [List.head?_map,finRange_head] at hb
    simp only [Option.map_some,Option.mem_def,Option.some.injEq] at ha hb
    subst a; subst b
    apply canonicalCell_pair bits bits
    change q-1+1=q
    have := NeZero.pos q
    omega
  · intro a ha b hb
    simp only [List.getLast?_append,List.getLast?_map,finRange_last,
      Option.map_some,Option.or_some,Option.mem_def,Option.some.injEq] at ha
    simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hb
    subst a; subst b
    apply canonicalCell_pair bits bits
    trivial

lemma canonicalBlock_head (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).head? = some (canonicalCell bits (.core 0)) := by
  simp [canonicalBlock,List.head?_append,List.head?_map,finRange_head]

lemma canonicalBlock_last (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).getLast? = some (canonicalCell bits .stop) := by
  simp [canonicalBlock,List.getLast?_append]

lemma encodeWord_pair_chain (w : List (Fin d → ZMod 2)) :
    (encodeWord (q:=q) w).IsChain Pair := by
  induction w with
  | nil => simp [encodeWord]
  | cons b w ih =>
    change (canonicalBlock b ++ encodeWord w).IsChain Pair
    apply (canonicalBlock_pair_chain b).append ih
    intro a ha c hc
    rw [canonicalBlock_last] at ha
    simp only [Option.mem_def,Option.some.injEq] at ha
    subst a
    cases w with
    | nil => simp [encodeWord] at hc
    | cons b' w =>
      have he : (encodeWord (b'::w)).head? = some (canonicalCell b' (.core (0 : Fin q))) := by
        change (canonicalBlock b' ++ encodeWord w).head? = _
        rw [List.head?_append,canonicalBlock_head]
        rfl
      rw [he] at hc
      simp only [Option.mem_def,Option.some.injEq] at hc
      subst c
      exact canonicalCell_pair b b' .stop (.core 0) rfl

omit [NeZero q] in
lemma closed_of_pair_chain (w : List (Skeleton q 10))
    (ha : ∀ c ∈ w, c.Admissible) (hc : w.IsChain Skeleton.Pair)
    (hl : ∀ c ∈ w.head?, c.leftExternal) (hr : ∀ c ∈ w.getLast?, c.rightExternal) :
    Skeleton.Closed w := by
  refine ⟨ha,?_⟩
  have hm : (w.map some).IsChain Skeleton.Link := by
    simpa only [List.isChain_map,Skeleton.Link] using hc
  have ht : (w.map some ++ [none]).IsChain Skeleton.Link := by
    apply hm.append (List.isChain_singleton _)
    intro a hea b heb
    simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at heb
    subst b
    cases he : w.getLast? with
    | none => simp [List.getLast?_map,he] at hea
    | some c =>
      simp only [List.getLast?_map,he,Option.map_some,Option.mem_def,Option.some.injEq] at hea
      subst a
      exact hr c (by simp [he])
  apply ht.cons
  intro a hea
  cases w with
  | nil =>
    simp only [List.map_nil,List.nil_append,List.head?_cons, Option.mem_def,Option.some.injEq] at hea
    subst a
    trivial
  | cons c w =>
    simp only [List.map_cons,List.cons_append,List.head?_cons,Option.mem_def,Option.some.injEq] at hea
    subst a
    exact hl c (by simp)

lemma encodeWord_syntax (w : List (Fin d → ZMod 2)) :
    Syntax S d (encodeWord (q:=q) w) := by
  have hf : ∀ c ∈ encodeWord (q:=q) w, c.Format S d := by
    intro c hc
    obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hc
    exact canonicalBlock_format b c hc
  have hi : ∀ c ∈ encodeWord (q:=q) w, c.marker=.idle := by
    intro c hc
    obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hc
    simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
    rcases hc with (⟨p,_,rfl⟩|⟨x,_,rfl⟩)|rfl <;> rfl
  have hchain := encodeWord_pair_chain (q:=q) w
  refine ⟨?_,hchain.imp (fun _ _ h => h.2),hf⟩
  apply closed_of_pair_chain
  · intro s hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
    exact (hf c hc).1
  · simpa only [List.isChain_map] using hchain.imp (fun _ _ h => h.1)
  · intro s hs
    have hs' := List.mem_of_mem_head? hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs'
    exact Or.inl (hi c hc)
  · intro s hs
    have hs' := List.mem_of_mem_getLast? hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs'
    exact Or.inl (hi c hc)

end SourceBurnside.FiniteTable

end

end OAI
