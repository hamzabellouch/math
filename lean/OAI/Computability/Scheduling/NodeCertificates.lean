import OAI.Computability.Scheduling.PriorityUpdates

namespace OAI

section

namespace ThreeMachine.Structure
section NodeCertificates
variable {J A : Type} [Fintype J] [DecidableEq J]

structure NodeData (r : J → J → Prop) (rank : J → ℕ) (atoms : A → Set J)
    (p : Layout J) (W : Set J) where
  full : p.Full r
  a : ℕ
  b : ℕ
  left : Boundary J
  right : Boundary J
  leftAt : left.At p.time (Fintype.card J / 3) a
  rightAt : right.At p.time (Fintype.card J / 3) b
  window : ∀ x, x ∈ W ↔ x ∈ Window p.time a b
  list : GlobalList J
  run : RunData list rank atoms W
  upsets : list.Upsets r
  second_upset : GlobalUpset r run.second
  disjoint : list.InjectionDisjoint W
  length : list.indices.card ≤ 5
  high : ∀ x ∈ W, x ∈ list.Qual → x ∈ right.pred r
  low : ∀ x ∈ W, x ∉ list.Qual → x ∈ left.desc r
  past : PastInvariant r p.time list left a
  swap : SwapInvariant r p W list rank left a
  small : Described atoms W 406
  reverseSeed : ReverseSeed r p.time atoms W right b

namespace NodeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

def reorder (D : NodeData r rank atoms p W) (hfix : p.FixedOutside q W)
    (hq : q.Respects r) : NodeData r rank atoms q W :=
  { D with
    full := ⟨D.full.1, hq⟩
    leftAt := hfix.boundary D.window (Or.inl le_rfl) D.leftAt
    rightAt := hfix.boundary D.window (Or.inr le_rfl) D.rightAt
    window := hfix.window D.window
    past := D.past.reorder hfix D.window
    swap := D.swap.reorder hfix
    reverseSeed := D.reverseSeed.reorder (Set.ext D.window) hfix }

theorem cover (D : NodeData r rank atoms p W) :
    ∀ x ∈ W, x ∈ D.left.desc r ∨ x ∈ D.right.pred r := by
  intro x hx
  by_cases hq : x ∈ D.list.Qual
  · exact Or.inr (D.high x hx hq)
  · exact Or.inl (D.low x hx hq)

noncomputable def root (p : Layout J) (hp : p.Full r)
    (hA : AtomSupport atoms r rank) : NodeData r rank atoms p Set.univ := by
  refine { full := hp, a := 0, b := Fintype.card J / 3 + 1
           left := .left, right := .right, leftAt := rfl, rightAt := rfl
           window := ?_, list := .one Set.univ, run := RunData.root hA.truth
           upsets := ?_, second_upset := ?_, disjoint := ?_, length := ?_
           high := ?_, low := ?_, past := ?_, swap := ?_
           small := hA.truth.mono (by omega), reverseSeed := ?_ }
  · intro x
    have := p.time_bounds hp.1 x
    simp only [Set.mem_univ, Window, Set.mem_ofPred_eq, true_iff]
    omega
  · intro i _ x y _ _
    trivial
  · intro x y _ _
    trivial
  · intro i hi h2i
    simp only [GlobalList.one, Finset.mem_singleton] at hi
    omega
  · simp [GlobalList.one]
  · intro x _ _
    trivial
  · intro x _ _
    trivial
  · intro x _ htime
    have := (p.time_bounds hp.1 x).1
    omega
  · intro q _ _ x _ _ y hy
    have := (q.time_bounds hp.1 y).1
    omega
  · refine ⟨Set.univ, ?_, hA.truth.mono (by omega), ?_, ?_⟩
    · intro x y _ _
      trivial
    · intro x _ _
      trivial
    · intro x _
      have := (p.time_bounds hp.1 x).2
      omega

end NodeData

structure EdgeData (r : J → J → Prop) (rank : J → ℕ) (atoms : A → Set J)
    (p : Layout J) (W : Set J) (a b v ap bp : ℕ)
    (B V A' B' : Boundary J) where
  full : p.Full r
  parent : W = Window p.time a b
  endAt : B.At p.time (Fintype.card J / 3) b
  centerAt : V.At p.time (Fintype.card J / 3) v
  startAt : A'.At p.time (Fintype.card J / 3) ap
  targetAt : B'.At p.time (Fintype.card J / 3) bp
  targetActual : ∃ Z, B' = Boundary.actual Z
  start_le : a ≤ ap
  strict : ap < bp
  target_le : bp ≤ v
  center_lt : v < b
  cutoff : Set J
  finalCutoff : Set J
  finalSmall : Described atoms finalCutoff 1
  centerSep : V.Separates r p.time W finalCutoff v
  startSep : A'.Separates r p.time (Window p.time a v) cutoff ap
  targetSep : B'.Separates r p.time (Window p.time a v) cutoff bp
  covers : ∀ x ∈ W, x ∈ cutoff → x ∈ B.pred r
  below : ∀ x ∈ W, x ∈ cutoff → x ∈ finalCutoff
  list : GlobalList J
  run : RunData list rank atoms W
  upsets : list.Upsets r
  second_upset : GlobalUpset r run.second
  disjoint : list.InjectionDisjoint W
  labels : ∀ x ∈ W, x ∈ list.Qual ↔ x ∉ cutoff
  past : PastInvariant r p.time list A' ap
  swap : SwapInvariant r p (Window p.time ap bp) list rank A' ap
  globalCutoff : Set J
  cutoffSmall : Described atoms globalCutoff 205
  cutoffAgrees : ∀ x ∈ W, x ∈ globalCutoff ↔ x ∈ cutoff
  lowExtension : Set J
  downset : GlobalUpset (fun x y => r y x) lowExtension
  lowSmall : Described atoms lowExtension 21
  lowAgrees : ∀ x ∈ W, x ∈ lowExtension ↔ x ∈ cutoff

namespace EdgeData
variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {a b v ap bp : ℕ} {B V A' B' : Boundary J}

noncomputable def toNode
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B')
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) :
    NodeData r rank atoms p (Window p.time ap bp) := by
  let W' := Window p.time ap bp
  have hsub : W' ⊆ W := by
    intro x hx
    rw [D.parent]
    exact ⟨D.start_le.trans_lt hx.1, hx.2.trans_le D.target_le |>.trans D.center_lt⟩
  have hE : W' ⊆ Window p.time a v := by
    intro x hx
    exact ⟨D.start_le.trans_lt hx.1, hx.2.trans_le D.target_le⟩
  have hhigh : ∀ x ∈ W', x ∉ D.cutoff → x ∈ B'.pred r := by
    intro x hx hn
    exact D.targetSep.1 x (hE hx) hx.2 hn
  have hlow : ∀ x ∈ W', x ∈ D.cutoff → x ∈ A'.desc r ∩ B.pred r := by
    intro x hx hS
    exact ⟨D.startSep.2 x (hE hx) hx.1 hS, D.covers x (hsub hx) hS⟩
  let K' := D.list.prune W'
  let R' := D.run.prune hsub
  have hqual : ∀ x ∈ W', x ∈ K'.Qual ↔ x ∉ D.cutoff := by
    intro x hx
    exact (GlobalList.prune_qual D.list hx).trans (D.labels x (hsub hx))
  have hlength : K'.indices.card ≤ 5 := by
    obtain ⟨Z, hZ⟩ := D.targetActual
    apply GlobalList.pruned_length D.upsets D.disjoint (B := Z)
    · intro z hz
      have ht : p.time z = bp := (show (Boundary.actual Z).At p.time
        (Fintype.card J / 3) bp from hZ ▸ D.targetAt).2.2 z |>.mp hz
      rw [D.parent]
      exact ⟨by have := D.start_le; have := D.strict; omega,
        by have := D.target_le; have := D.center_lt; omega⟩
    · intro x hx hq
      have h := hhigh x hx ((D.labels x (hsub hx)).mp hq)
      simpa only [hZ, Boundary.pred, Set.mem_ofPred_eq] using h
  have hpast : PastInvariant r p.time K' A' ap := past_prune D.past
  have hh := global_high_identity D.full.2 (p.time_bounds D.full.1)
    D.startAt D.targetAt hqual hhigh hpast
  have hl := global_low_identity D.full.2 (p.time_bounds D.full.1)
    D.startAt D.endAt D.targetAt D.centerAt D.start_le D.strict D.target_le D.center_lt
    (fun x hx => D.cutoffAgrees x (D.parent ▸ hx))
    (fun x hx => D.below x (D.parent ▸ hx))
    (D.parent ▸ D.centerSep) D.targetSep hlow
  have hsmall : Described atoms W' 406 := global_child_small hA
    (R'.qual_small hA hlength) D.cutoffSmall hh hl
  have hseedExists := reverse_seed_at_edge htrans D.full.2 (p.time_bounds D.full.1)
    D.endAt D.targetAt D.centerAt D.parent rfl rfl D.start_le D.strict D.target_le D.center_lt
    hhigh D.covers D.below D.centerSep D.targetSep D.downset D.lowAgrees D.lowSmall
    (hA.pred B) (hA.weakDesc B') (hA.weakDesc V)
  exact { full := D.full, a := ap, b := bp, left := A', right := B'
          leftAt := D.startAt, rightAt := D.targetAt, window := fun _ => Iff.rfl
          list := K', run := R', upsets := GlobalList.prune_upsets D.upsets
          second_upset := D.second_upset, disjoint := D.disjoint.prune hsub, length := hlength
          high := fun x hx hq => hhigh x hx ((hqual x hx).mp hq)
          low := fun x hx hn => (hlow x hx (by by_contra h; exact hn ((hqual x hx).mpr h))).1
          past := hpast, swap := swap_prune D.swap, small := hsmall, reverseSeed := Classical.choice hseedExists }

end EdgeData
end NodeCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace Boundary
variable {J : Type} {time : J → ℕ} {T s : ℕ}

theorem at_le {B : Boundary J} (hB : B.At time T s) : s ≤ T+1 := by
  cases B with
  | left => simp only [At] at hB; omega
  | right => exact hB.le
  | actual Z => exact hB.2.1.trans (by omega)

theorem at_unique {B C : Boundary J} (hB : B.At time T s) (hC : C.At time T s) :
    B = C := by
  cases B <;> cases C <;> try rfl
  all_goals simp only [At] at hB hC
  all_goals try omega
  congr 1
  apply Subtype.ext
  ext x
  exact (hB.2.2 x).trans (hC.2.2 x).symm

end Boundary

section SameEdges
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

theorem exists_same_edge (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank)
    {B t v ap bp : ℕ} {V A' B' : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hap : D.a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hB' : B'.At p.time (Fintype.card J / 3) bp)
    (hactual : ∃ Z, B' = Boundary.actual Z)
    (ht : t ≤ (D.list.indices.sup id + 1) * B)
    (hnorm : p.NormalizedOn (Window p.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r)))
    (hstart : A'.Separates r p.time (Window p.time D.a v)
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) ap)
    (hend : B'.Separates r p.time (Window p.time D.a v)
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) bp)
    (E : Finset J) (hEwin : ∀ x, x ∈ E ↔ x ∈ Window p.time D.a v)
    (hwalk : CutoffWalk E r p.time
      (D.list.samePriority rank B (D.right.pred r))
      (PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)) D.a ap) :
    Nonempty (EdgeData r rank atoms p W D.a D.b v ap bp D.right V A' B') := by
  classical
  let S := PriorityCut (D.list.samePriority rank B (D.right.pred r)) (B+t)
  let K' := D.list.sameUpdate rank B t (D.left.desc r) (D.right.pred r)
  let H := D.right.pred r \ (D.list.carry rank (t/B) (t%B)).Qual
  have hagree : ∀ x ∈ W, x ∈ S ↔ x ∈ H :=
    GlobalList.samePriority_cut hB hrank D.high ht
  have hlabels : ∀ x ∈ W, x ∈ K'.Qual ↔ x ∉ S :=
    GlobalList.sameUpdate_agreement hB hrank D.high D.cover ht
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    exact (D.window x).mpr ⟨hap.trans_lt hx.1, (hx.2.trans_le hbp).trans hv.2⟩
  have hE : Window p.time ap bp ⊆ Window p.time D.a v := by
    intro x hx
    exact ⟨hap.trans_lt hx.1, hx.2.trans_le hbp⟩
  have hqual : ∀ x ∈ Window p.time ap bp, x ∉ A'.desc r → x ∈ K'.Qual := by
    intro x hx hn
    apply (hlabels x (hsub hx)).mpr
    intro hS
    exact hn (hstart.2 x (hE hx) hx.1 hS)
  have hswap : SwapInvariant r p (Window p.time ap bp) K' rank A' ap := by
    rcases hap.eq_or_lt with he | hl
    · have hAA : A' = D.left := Boundary.at_unique hA' (he ▸ D.leftAt)
      subst ap
      subst A'
      exact sameUpdate_swap_inherited D.full D.leftAt D.window hsub D.swap hqual
    · apply swap_from_normalized (fun _ => Iff.rfl) (fun _ => Iff.rfl) hl hbp hab hnorm hqual
      intro x hx hxK y hya hyK hkey
      have hyW : y ∈ W := (D.window y).mpr ⟨by omega,
        by have := hv.2; omega⟩
      exact (GlobalList.sameUpdate_key hrank D.high (hsub hx) hyW hxK hyK).mp hkey
  have hapos : D.a ≤ Fintype.card J / 3 := by
    have := Boundary.at_le D.rightAt
    omega
  have hEeq : (↑E : Set J) = Window p.time D.a v := Set.ext hEwin
  have hpast : PastInvariant r p.time K' A' ap := by
    apply sameUpdate_past D.full htrans D.leftAt hA' D.window
      (E := E) hEwin
      hv.2 hapos (hab.trans_le hbp) hB hrank hstrict D.upsets D.high D.low
      D.past D.swap ht
    · apply normalizedOn_local_obstruction
      · simpa only [hEeq] using hnorm
      · exact hEwin
    · simpa only [hEeq] using hstart
    · exact hwalk
  obtain ⟨Hext, hHup, hHsmall, hHagree⟩ := D.run.carry_low_extension hA D.length
    D.upsets D.second_upset hstrict htrans D.right (t/B) (t%B)
  refine ⟨{
    full := D.full, parent := Set.ext D.window, endAt := D.rightAt
    centerAt := hV, startAt := hA', targetAt := hB', targetActual := hactual
    start_le := hap, strict := hab, target_le := hbp, center_lt := hv.2
    cutoff := S, finalCutoff := D.right.pred r, finalSmall := hA.pred D.right, centerSep := hcenter
    startSep := hstart, targetSep := hend
    covers := fun x hx hs => ((hagree x hx).mp hs).1
    below := fun x hx hs => ((hagree x hx).mp hs).1
    list := K', run := (D.run.carry (t/B) (t%B)).append
        (D.left.desc r \ D.right.pred r) ((hA.desc D.left).diff (hA.pred D.right))
    upsets := GlobalList.sameUpdate_upsets D.upsets
        (Boundary.desc_upset htrans D.left) (fun _ _ hxy hx => Boundary.pred_downset htrans D.right hxy hx) hstrict
    second_upset := D.second_upset
    disjoint := GlobalList.sameUpdate_disjoint D.disjoint D.high
    labels := hlabels, past := hpast, swap := hswap
    globalCutoff := H, cutoffSmall := D.run.carry_cutoff_small hA D.length D.right (t/B) (t%B)
    cutoffAgrees := fun x hx => (hagree x hx).symm
    lowExtension := Hext, downset := hHup, lowSmall := hHsmall
    lowAgrees := fun x hx => (hHagree x hx).trans (hagree x hx).symm }⟩

end SameEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchedEdges
variable {J A : Type} [Fintype J] [DecidableEq J]

structure SwitchSeed (r : J → J → Prop) (time : J → ℕ) (atoms : A → Set J)
    (W : Set J) (B : Boundary J) (a : ℕ) where
  predicate : Set J
  upset : GlobalUpset r predicate
  small : Described atoms predicate 24
  cover : ∀ x ∈ W, x ∉ B.desc r → x ∈ predicate
  later : ∀ x ∈ predicate, a < time x

variable {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J}

def ReverseSeed.toSwitch {B : Boundary J} {b : ℕ}
    (D : ReverseSeed r p.time atoms W B b) (hfull : 3 ∣ Fintype.card J)
    (hb : b ≤ Fintype.card J / 3 + 1) :
    SwitchSeed (fun x y => r y x) p.reverse.time atoms W B.reverse
      (Fintype.card J / 3 + 1 - b) := by
  refine { predicate := D.predicate, upset := D.downset, small := D.small
           cover := ?_, later := ?_ }
  · simpa only [Boundary.desc_reverse] using D.cover
  · intro x hx
    rw [Layout.reverse_time p hfull]
    have := D.earlier x hx
    have := p.time_bounds hfull x
    omega

theorem exists_switch_edge {a b v ap bp B t : ℕ} {L R V A' B' : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hap : a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
    (hA' : A'.At p.time (Fintype.card J / 3) ap)
    (hB' : B'.At p.time (Fintype.card J / 3) bp)
    (hactual : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ B)
    (hnorm : p.NormalizedOn (Window p.time a v) r (switchPriority rank B (L.desc r)))
    (hstart : A'.Separates r p.time (Window p.time a v)
      (PriorityCut (switchPriority rank B (L.desc r)) t) ap)
    (hend : B'.Separates r p.time (Window p.time a v)
      (PriorityCut (switchPriority rank B (L.desc r)) t) bp) :
    Nonempty (EdgeData r rank atoms p W a b v ap bp R V A' B') := by
  classical
  let S := PriorityCut (switchPriority rank B (L.desc r)) t
  let K' := GlobalList.pair (G.predicate ∩ RankTail rank t) (L.desc r)
  have hlabels : ∀ x ∈ W, x ∈ K'.Qual ↔ x ∉ S :=
    GlobalList.switchPair_agreement ht G.cover
  have hcut : S = (L.desc r)ᶜ \ RankTail rank t := switchPriority_cut ht
  have hsup : GlobalUpset r (L.desc r) := Boundary.desc_upset htrans L
  have hK : K'.Upsets r := GlobalList.pair_upsets
    (fun _ _ hxy hx => ⟨G.upset hxy hx.1, rankTail_upset hstrict t hxy hx.2⟩) hsup
  have hnonearly : ∀ x ∈ K'.Qual, a < p.time x := by
    intro x hx
    rw [GlobalList.qual_pair] at hx
    rcases hx with hx | hx
    · exact G.later x hx.1
    · exact Boundary.desc_time hp.2 (p.time_bounds hp.1) hL hx
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    exact (hW x).mpr ⟨hap.trans_lt hx.1, (hx.2.trans_le hbp).trans hv.2⟩
  have hE : Window p.time ap bp ⊆ Window p.time a v := by
    intro x hx
    exact ⟨hap.trans_lt hx.1, hx.2.trans_le hbp⟩
  have hqual : ∀ x ∈ Window p.time ap bp, x ∉ A'.desc r → x ∈ K'.Qual := by
    intro x hx hn
    apply (hlabels x (hsub hx)).mpr
    intro hS
    exact hn (hstart.2 x (hE hx) hx.1 hS)
  have hpast : PastInvariant r p.time K' A' ap := by
    intro x hx ht'
    have hax := hnonearly x hx
    have hxE : x ∈ Window p.time a v := ⟨hax, ht'.trans_lt (hab.trans_le hbp)⟩
    rcases ht'.eq_or_lt with he | hl
    · exact (Boundary.mem_weak_at_time (p.time_bounds hp.1) hA' he).1
    · have hxW : x ∈ W := (hW x).mpr ⟨hax, hxE.2.trans hv.2⟩
      exact A'.pred_subset_weakPred r (hstart.1 x hxE hl ((hlabels x hxW).mp hx))
  have hswap : SwapInvariant r p (Window p.time ap bp) K' rank A' ap := by
    rcases hap.eq_or_lt with he | hl
    · intro q hfix _ x _ _ y hy hyK
      have hnW : y ∉ Window p.time ap bp := by
        intro hyW
        have h := (hfix.window (fun _ => Iff.rfl) y).mp hyW
        have := h.1
        omega
      have hya : p.time y = a := by rw [← hfix.time hnW, hy]; omega
      have := hnonearly y hyK
      omega
    · apply swap_from_normalized (fun _ => Iff.rfl) (fun _ => Iff.rfl) hl hbp hab hnorm hqual
      intro x _ _ y _ _ hkey
      exact (GlobalList.switchPair_key hrank x y).mp hkey
  have hSsmall : Described atoms S 2 := by
    rw [hcut]
    exact (hA.desc L).compl.diff (hA.rankTail t)
  have hSdown : GlobalUpset (fun x y => r y x) S := by
    rw [hcut]
    intro x y hyx hx
    exact ⟨fun hyD => hx.1 (hsup hyx hyD), fun hyr =>
      hx.2 (rankTail_upset hstrict t hyx hyr)⟩
  refine ⟨{
    full := hp, parent := Set.ext hW, endAt := hR, centerAt := hV
    startAt := hA', targetAt := hB', targetActual := hactual
    start_le := hap, strict := hab, target_le := hbp, center_lt := hv.2
    cutoff := S, finalCutoff := (L.desc r)ᶜ, finalSmall := (hA.desc L).compl, centerSep := hcenter
    startSep := hstart, targetSep := hend, covers := ?_, below := ?_
    list := K', run := RunData.switched G.small (hA.desc L) G.cover t
    upsets := hK, second_upset := hsup, disjoint := ?_, labels := hlabels
    past := hpast, swap := hswap, globalCutoff := S
    cutoffSmall := hSsmall.mono (by omega), cutoffAgrees := fun _ _ => Iff.rfl
    lowExtension := S, downset := hSdown, lowSmall := hSsmall.mono (by omega)
    lowAgrees := fun _ _ => Iff.rfl }⟩
  · intro x hx hS
    rw [hcut] at hS
    exact (hcover x hx).resolve_left hS.1
  · intro x _ hS
    rw [hcut] at hS
    exact hS.1
  · intro i hi h2i
    simp only [K', GlobalList.pair, Finset.mem_insert, Finset.mem_singleton] at hi
    omega

end SwitchedEdges
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Centers
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J}

omit [DecidableEq J] in

theorem window_first_slot {a b : ℕ} (hp : p.Full r)
    (hne : (Window p.time a b).Nonempty) :
    ∃ x ∈ Window p.time a b, p.time x = a+1 := by
  obtain ⟨y, hy⟩ := hne
  change a < p.time y ∧ p.time y < b at hy
  have hybound := p.time_bounds hp.1 y
  have hb : a+1 ≤ Fintype.card J / 3 := by omega
  have hc := p.card_slot hp.1 (a+1) (by omega) hb
  have hn : (p.slot (a+1)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hn
  have hx' := (p.mem_slot (a+1) x).mp hx
  exact ⟨x, ⟨by omega, by omega⟩, hx'⟩

theorem exists_node_center (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z) (hne : W.Nonempty) :
    ∃ q : Layout J, ∃ _hfix : p.FixedOutside q W, q.Respects r ∧
      ∃ (v : ℕ) (V : Boundary J), D.a < v ∧ v < D.b ∧
        V.At q.time (Fintype.card J / 3) v ∧
        V.Separates r q.time W (D.right.pred r) v := by
  classical
  let priority := fun x : J => if x ∈ D.right.pred r then (p x).val
    else Fintype.card J + (p x).val
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p W r priority D.full.2
  let Dq := D.reorder hfix hnorm.1
  have hwindow : ∀ x, x ∈ W ↔ x ∈ Window q.time D.a D.b := Dq.window
  let E := W.toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ W := by intro x; simp [E]
  have hEeq : (↑E : Set J) = W := Set.ext hE
  have hclosed : SlotClosed E q.time := by
    intro x hx y hxy
    apply (hE y).mpr
    have h := (hwindow x).mp ((hE x).mp hx)
    exact (hwindow y).mpr (by simpa only [Window, Set.mem_ofPred, ← hxy] using h)
  have hideal : IdealOn E r (D.right.pred r) := by
    intro x _ y _ hxy hy
    exact Boundary.pred_downset htrans D.right hxy hy
  have hprefix : PrefixOn E priority (D.right.pred r) := by
    intro x _ hx y _ hy
    simp only [priority, ite_eq_left hx, ite_eq_right hy]
    have := (p x).isLt
    omega
  have hne' : (Window q.time D.a D.b).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hwindow x).mp hx⟩
  obtain ⟨x, hx, hxa⟩ := window_first_slot Dq.full hne'
  have hnormE : LocalObstruction E r q.time priority := by
    apply normalizedOn_local_obstruction
    · simpa only [hEeq] using hnorm
    · intro x
      exact (hE x).trans (hwindow x)
  have hfirst : EarlierHigh E r q.time (D.right.pred r) (D.a+1) := by
    intro x hx htime _
    have := ((hwindow x).mp ((hE x).mp hx)).1
    omega
  obtain ⟨v, _, hpath, hsep⟩ := walk_to_separator htrans hnorm.1 hclosed
    (Or.inl ⟨x, (hE x).mpr ((hwindow x).mpr hx), hxa⟩) hideal hprefix hnormE hfirst
  have hv : ∃ z ∈ W, q.time z = v := by
    rcases hpath.endpoint with he | ⟨z, hz, he⟩
    · exact ⟨x, (hwindow x).mpr hx, hxa.trans he.symm⟩
    · exact ⟨z, (hE z).mp hz, he⟩
  obtain ⟨z, hz, hzv⟩ := hv
  have hvwin := (hwindow z).mp hz
  have hvlo := hvwin.1
  have hvhi := hvwin.2
  have hvbound := q.time_bounds D.full.1 z
  have hva : D.a < v := by omega
  have hvb : v < D.b := by omega
  have hvpos : 1 ≤ v := by omega
  have hvle : v ≤ Fintype.card J / 3 := by omega
  let V := Boundary.actual (q.triple D.full.1 v hvpos hvle)
  have hV : V.At q.time (Fintype.card J / 3) v := q.triple_at D.full.1 v hvpos hvle
  refine ⟨q, hfix, hnorm.1, v, V, hva, hvb, hV, ?_⟩
  simpa only [hEeq] using (Boundary.actual_separates hV).mpr hsep

omit [DecidableEq J] in

theorem Layout.FixedOutside.before_iff {U : Set J} {a b s : ℕ}
    (hfix : p.FixedOutside q U) (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (x : J) : p.time x < s ↔ q.time x < s := by
  by_cases hx : x ∈ U
  · have hp := (hU x).mp hx
    have hq := (hfix.window hU x).mp hx
    rcases hs with hs | hs <;> dsimp [Window] at hp hq <;> omega
  · rw [hfix.time hx]

omit [DecidableEq J] in
theorem Layout.FixedOutside.after_iff {U : Set J} {a b s : ℕ}
    (hfix : p.FixedOutside q U) (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b)
    (hs : s ≤ a ∨ b ≤ s) (x : J) : s < p.time x ↔ s < q.time x := by
  by_cases hx : x ∈ U
  · have hp := (hU x).mp hx
    have hq := (hfix.window hU x).mp hx
    rcases hs with hs | hs <;> dsimp [Window] at hp hq <;> omega
  · rw [hfix.time hx]

omit [DecidableEq J] in
theorem Boundary.Separates.reorder {U S : Set J} {a b s : ℕ} {V : Boundary J}
    (hsep : V.Separates r p.time W S s) (hfix : p.FixedOutside q U)
    (hU : ∀ x, x ∈ U ↔ x ∈ Window p.time a b) (hs : s ≤ a ∨ b ≤ s) :
    V.Separates r q.time W S s := by
  constructor
  · intro x hx htime hn
    exact hsep.1 x hx ((hfix.before_iff hU hs x).mpr htime) hn
  · intro x hx htime hS
    exact hsep.2 x hx ((hfix.after_iff hU hs x).mpr htime) hS

end Centers
end ThreeMachine.Structure

end

end OAI
