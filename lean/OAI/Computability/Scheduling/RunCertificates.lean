import OAI.Computability.Scheduling.FrameInvariants

namespace OAI

section

namespace ThreeMachine.Structure
section RunCertificates
variable {J A : Type}

def RankTail (rank : J → ℕ) (k : ℕ) : Set J := {x | k ≤ rank x}

theorem rankTail_upset {r : J → J → Prop} {rank : J → ℕ}
    (hrank : ∀ x y, r x y → rank x < rank y) (k : ℕ) :
    GlobalUpset r (RankTail rank k) := by
  intro x y hxy hx
  exact hx.trans (hrank x y hxy).le

structure RunData (K : GlobalList J) (rank : J → ℕ) (atoms : A → Set J)
    (W : Set J) where
  base : ℕ → Set J
  threshold : ℕ → ℕ
  second : Set J
  entry_eq : ∀ i ∈ K.indices, K.entry i = base i ∩ RankTail rank (threshold i)
  simple : ∀ i ∈ K.indices, i ≠ 0 → Described atoms (base i) 2
  first_small : Described atoms (base 0) 24
  second_small : Described atoms second 1
  second_eq : base 1 = second
  cover : ∀ x ∈ W, x ∉ second → x ∈ base 0
  pair : 0 ∈ K.indices → ∀ x ∈ W, x ∈ second → 1 ∈ K.indices ∧ x ∈ K.entry 1

namespace RunData
variable {K : GlobalList J} {rank : J → ℕ} {atoms : A → Set J} {W W' : Set J}

def narrow (D : RunData K rank atoms W) (hsub : W' ⊆ W) : RunData K rank atoms W' :=
  { D with
    cover := fun x hx hn => D.cover x (hsub hx) hn
    pair := fun hi x hx hD => D.pair hi x (hsub hx) hD }

noncomputable def carry (D : RunData K rank atoms W) (d k : ℕ) :
    RunData (K.carry rank d k) rank atoms W := by
  classical
  refine { base := D.base
           threshold := fun i => if i = d then max (D.threshold i) k else D.threshold i
           second := D.second
           entry_eq := ?_
           simple := ?_
           first_small := D.first_small
           second_small := D.second_small
           second_eq := D.second_eq
           cover := D.cover
           pair := ?_ }
  · intro i hi
    have hi' : i ∈ K.indices ∧ d ≤ i := Finset.mem_filter.mp hi
    change (if i = d then K.entry i ∩ {x | k ≤ rank x} else K.entry i) = _
    rw [D.entry_eq i hi'.1]
    by_cases hid : i = d
    · simp only [hid, ite_eq_left]
      ext x
      simp only [Set.mem_inter_iff, RankTail, Set.mem_ofPred_eq, max_le_iff]
      tauto
    · simp only [hid, ite_false]
  · intro i hi hn
    exact D.simple i (Finset.mem_filter.mp hi).1 hn
  · intro hzero x hx hxD
    have hd : d = 0 := by have := (Finset.mem_filter.mp hzero).2; omega
    have hz : 0 ∈ K.indices := (Finset.mem_filter.mp hzero).1
    obtain ⟨h1, hx1⟩ := D.pair hz x hx hxD
    refine ⟨Finset.mem_filter.mpr ⟨h1, by omega⟩, ?_⟩
    change x ∈ if 1 = d then _ else _
    simpa [hd] using hx1

noncomputable def prune (D : RunData K rank atoms W) (hsub : W' ⊆ W) :
    RunData (K.prune W') rank atoms W' := by
  classical
  refine { base := D.base, threshold := D.threshold, second := D.second
           entry_eq := ?_, simple := ?_, first_small := D.first_small
           second_small := D.second_small, second_eq := D.second_eq
           cover := fun x hx hn => D.cover x (hsub hx) hn
           pair := ?_ }
  · intro i hi
    exact D.entry_eq i (Finset.mem_filter.mp hi).1
  · intro i hi hn
    exact D.simple i (Finset.mem_filter.mp hi).1 hn
  · intro hzero x hx hxD
    obtain ⟨h1, hx1⟩ := D.pair (Finset.mem_filter.mp hzero).1 x (hsub hx) hxD
    exact ⟨Finset.mem_filter.mpr ⟨h1, ⟨x, hx1, hx⟩⟩, hx1⟩

noncomputable def append (D : RunData K rank atoms W) (I : Set J)
    (hI : Described atoms I 2) : RunData (K.append I) rank atoms W := by
  classical
  have hnext : 2 ≤ K.nextIndex := by dsimp [GlobalList.nextIndex]; omega
  refine { base := fun i => if i = K.nextIndex then I else D.base i
           threshold := fun i => if i = K.nextIndex then 0 else D.threshold i
           second := D.second
           entry_eq := ?_, simple := ?_, first_small := ?_
           second_small := D.second_small, second_eq := ?_
           cover := ?_, pair := ?_ }
  · intro i hi
    change i ∈ insert K.nextIndex K.indices at hi
    change (if i = K.nextIndex then I else K.entry i) = _
    by_cases he : i = K.nextIndex
    · simp only [he, ite_eq_left]
      ext x
      simp [RankTail]
    · have hiK : i ∈ K.indices := (Finset.mem_insert.mp hi).resolve_left he
      simpa only [he, ite_false] using D.entry_eq i hiK
  · intro i hi hn
    change i ∈ insert K.nextIndex K.indices at hi
    by_cases he : i = K.nextIndex
    · simpa only [he, ite_eq_left] using hI
    · simpa only [he, ite_false] using D.simple i ((Finset.mem_insert.mp hi).resolve_left he) hn
  · simpa only [show 0 ≠ K.nextIndex by omega, ite_false] using D.first_small
  · simpa only [show 1 ≠ K.nextIndex by omega, ite_false] using D.second_eq
  · intro x hx hn
    simpa only [show 0 ≠ K.nextIndex by omega, ite_false] using D.cover x hx hn
  · intro hz x hx hxD
    change 0 ∈ insert K.nextIndex K.indices at hz
    have hzK : 0 ∈ K.indices := (Finset.mem_insert.mp hz).resolve_left (by omega)
    obtain ⟨h1, hx1⟩ := D.pair hzK x hx hxD
    refine ⟨Finset.mem_insert_of_mem h1, ?_⟩
    change x ∈ if 1 = K.nextIndex then I else K.entry 1
    simpa only [show 1 ≠ K.nextIndex by omega, ite_false] using hx1

theorem entry_small (D : RunData K rank atoms W)
    (hrank : ∀ k, Described atoms (RankTail rank k) 1) {i : ℕ} (hi : i ∈ K.indices) :
    Described atoms (K.entry i) 25 := by
  rw [D.entry_eq i hi]
  by_cases he : i = 0
  · subst i
    exact D.first_small.inter (hrank _)
  · exact ((D.simple i hi he).inter (hrank _)).mono (by omega)

noncomputable def flatEntry (D : RunData K rank atoms W) (i : ℕ) : Set J :=
  if i = 0 then D.second ∪ RankTail rank (D.threshold 0) else K.entry i

theorem flat_union_agrees (D : RunData K rank atoms W) :
    ∀ x ∈ W, (∃ i ∈ K.indices, x ∈ D.flatEntry i) ↔ x ∈ K.Qual := by
  classical
  intro x hx
  constructor
  · rintro ⟨i, hi, hxi⟩
    by_cases he : i = 0
    · subst i
      change x ∈ if 0 = 0 then _ else _ at hxi
      rcases hxi with hD | htail
      · obtain ⟨h1, hx1⟩ := D.pair hi x hx hD
        exact ⟨1, h1, hx1⟩
      · by_cases hD : x ∈ D.second
        · obtain ⟨h1, hx1⟩ := D.pair hi x hx hD
          exact ⟨1, h1, hx1⟩
        · refine ⟨0, hi, ?_⟩
          rw [D.entry_eq 0 hi]
          exact ⟨D.cover x hx hD, htail⟩
    · exact ⟨i, hi, by simpa only [flatEntry, he, ite_false] using hxi⟩
  · rintro ⟨i, hi, hxi⟩
    refine ⟨i, hi, ?_⟩
    by_cases he : i = 0
    · subst i
      dsimp only [flatEntry]
      exact Or.inr ((D.entry_eq 0 hi) ▸ hxi).2
    · simpa only [flatEntry, he, ite_false] using hxi

theorem short_upset_extension (D : RunData K rank atoms W) {r : J → J → Prop}
    (hK : K.Upsets r) (hD : GlobalUpset r D.second)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hrank : ∀ k, Described atoms (RankTail rank k) 1)
    (hfalse : Described atoms ∅ 1) (hcard : K.indices.card ≤ 5) :
    ∃ H : Set J, GlobalUpset r H ∧ Described atoms H 20 ∧
      ∀ x ∈ W, x ∈ H ↔ x ∈ K.Qual := by
  classical
  let H : Set J := {x | ∃ i ∈ K.indices, x ∈ D.flatEntry i}
  refine ⟨H, ?_, ?_, D.flat_union_agrees⟩
  · intro x y hxy hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine ⟨i, hi, ?_⟩
    by_cases he : i = 0
    · subst i
      exact (hD.union (rankTail_upset hstrict _)) hxy hxi
    · simp only [flatEntry, he, ite_false] at hxi ⊢
      exact hK i hi hxy hxi
  · by_cases hne : K.indices.Nonempty
    · have hsmall : ∀ i ∈ K.indices, Described atoms (D.flatEntry i) 4 := by
        intro i hi
        by_cases he : i = 0
        · subst i
          exact (D.second_small.union (hrank _)).mono (by omega)
        · simp only [flatEntry, he, ite_false]
          rw [D.entry_eq i hi]
          exact ((D.simple i hi he).inter (hrank _)).mono (by omega)
      have hh := Described.finite_union K.indices D.flatEntry (fun _ => 4) hne hsmall
      apply hh.mono
      simp only [Finset.sum_const, smul_eq_mul]
      omega
    · have he : K.indices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hH : H = ∅ := by ext x; simp [H, he]
      rw [hH]
      exact hfalse.mono (by omega)

end RunData
end RunCertificates
end ThreeMachine.Structure

namespace ThreeMachine.Structure
namespace GlobalList
variable {J : Type}

def empty : GlobalList J := ⟨∅, fun _ => ∅⟩

def one (A : Set J) : GlobalList J := ⟨{1}, fun _ => A⟩

def pair (A B : Set J) : GlobalList J := ⟨{0, 1}, fun i => if i = 0 then A else B⟩

@[simp] theorem qual_empty : (empty : GlobalList J).Qual = ∅ := by
  ext x
  simp [Qual, empty]

@[simp] theorem qual_one (A : Set J) : (one A).Qual = A := by
  ext x
  simp [Qual, one]

@[simp] theorem qual_pair (A B : Set J) : (pair A B).Qual = A ∪ B := by
  ext x
  simp [Qual, pair]

theorem empty_upsets (r : J → J → Prop) : (empty : GlobalList J).Upsets r := by
  intro i hi
  have hf : i ∈ (∅ : Finset ℕ) := hi
  simp at hf

theorem pair_upsets {r : J → J → Prop} {A B : Set J}
    (hA : GlobalUpset r A) (hB : GlobalUpset r B) : (pair A B).Upsets r := by
  intro i _
  dsimp [pair]
  split <;> assumption

def InjectionDisjoint (K : GlobalList J) (W : Set J) : Prop :=
  ∀ i ∈ K.indices, 2 ≤ i → ∀ j ∈ K.indices, 2 ≤ j → i ≠ j →
    ∀ x ∈ W, x ∈ K.entry i → x ∉ K.entry j

theorem InjectionDisjoint.narrow {K : GlobalList J} {W W' : Set J}
    (h : K.InjectionDisjoint W) (hsub : W' ⊆ W) : K.InjectionDisjoint W' := by
  intro i hi h2i j hj h2j hn x hx hxi hxj
  exact h i hi h2i j hj h2j hn x (hsub hx) hxi hxj

theorem InjectionDisjoint.carry {K : GlobalList J} {W : Set J} {rank : J → ℕ}
    (h : K.InjectionDisjoint W) (d k : ℕ) : (K.carry rank d k).InjectionDisjoint W := by
  intro i hi h2i j hj h2j hn x hx hxi hxj
  have hmi := (carry_membership K rank d k i x).mp
    ((mem_memberships _ x i).mpr ⟨hi, hxi⟩)
  have hmj := (carry_membership K rank d k j x).mp
    ((mem_memberships _ x j).mpr ⟨hj, hxj⟩)
  exact h i hmi.1 h2i j hmj.1 h2j hn x hx hmi.2.2.1 hmj.2.2.1

theorem InjectionDisjoint.prune {K : GlobalList J} {W W' : Set J}
    (h : K.InjectionDisjoint W) (hsub : W' ⊆ W) : (K.prune W').InjectionDisjoint W' := by
  classical
  intro i hi h2i j hj h2j hn x hx hxi hxj
  exact h i (Finset.mem_filter.mp hi).1 h2i j (Finset.mem_filter.mp hj).1 h2j hn
    x (hsub hx) hxi hxj

theorem InjectionDisjoint.append {K : GlobalList J} {W I : Set J}
    (h : K.InjectionDisjoint W) (hdisj : ∀ x ∈ W, x ∈ I → x ∉ K.Qual) :
    (K.append I).InjectionDisjoint W := by
  classical
  intro i hi h2i j hj h2j hn x hx hxi hxj
  have hmi := (append_membership K I i x).mp ((mem_memberships _ x i).mpr ⟨hi, hxi⟩)
  have hmj := (append_membership K I j x).mp ((mem_memberships _ x j).mpr ⟨hj, hxj⟩)
  rcases hmi with ⟨hi, hxi⟩ | ⟨hi, hxi⟩ <;>
    rcases hmj with ⟨hj, hxj⟩ | ⟨hj, hxj⟩
  · exact hn (hi.trans hj.symm)
  · exact hdisj x hx hxi ⟨j, hj, hxj⟩
  · exact hdisj x hx hxj ⟨i, hi, hxi⟩
  · exact h i hi h2i j hj h2j hn x hx hxi hxj

theorem pruned_length {K : GlobalList J} {r : J → J → Prop}
    {W W' : Set J} {B : Triple J}
    (hup : K.Upsets r) (hdisj : K.InjectionDisjoint W)
    (hB : ∀ z ∈ B.val, z ∈ W)
    (hhigh : ∀ x ∈ W', x ∈ K.Qual → ∃ z ∈ B.val, r x z) :
    (K.prune W').indices.card ≤ 5 := by
  classical
  let P := K.prune W'
  let I := P.indices.filter (2 ≤ ·)
  have hI : ∀ i ∈ I, i ∈ K.indices := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hactive : ∀ i ∈ I, ∃ x ∈ W', x ∈ K.entry i := by
    intro i hi
    obtain ⟨x, hxK, hxW⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    exact ⟨x, hxW, hxK⟩
  have hcap : I.card ≤ B.val.card := injection_card_bound (fun _ hi => hI _ hi) hup
    (fun _ hz => hB _ hz)
    (fun i hi j hj hn x hx hxi hxj => hdisj i (hI i hi) (Finset.mem_filter.mp hi).2
      j (hI j hj) (Finset.mem_filter.mp hj).2 hn x hx hxi hxj)
    (fun i hi => by obtain ⟨x, hxW, hxi⟩ := hactive i hi; exact ⟨x, hxi, hxW⟩)
    (fun x hx hxq => hhigh x hx hxq)
  have hsmall : (P.indices.filter (fun i => i < 2)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (t := {0, 1}) ?_) (by decide)
    intro i hi
    have hi2 := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsum := Finset.card_filter_add_card_filter_not (s := P.indices) (p := fun i => 2 ≤ i)
  have hnot : P.indices.filter (fun i => ¬2 ≤ i) = P.indices.filter (fun i => i < 2) := by
    simp only [not_le]
  rw [hnot] at hsum
  change I.card + _ = P.indices.card at hsum
  have hthree := B.property
  change (K.prune W').indices.card ≤ 5
  dsimp only [P] at hsum hsmall
  omega

end GlobalList

namespace RunData
variable {J A : Type} {rank : J → ℕ} {atoms : A → Set J} {W : Set J}

noncomputable def root (htrue : Described atoms Set.univ 1) :
    RunData (GlobalList.one Set.univ) rank atoms W := by
  refine { base := fun _ => Set.univ, threshold := fun _ => 0, second := Set.univ
           entry_eq := ?_, simple := ?_, first_small := htrue.mono (by omega)
           second_small := htrue, second_eq := rfl, cover := ?_, pair := ?_ }
  · intro i _
    ext x
    simp [GlobalList.one, RankTail]
  · intro i _ _
    exact htrue.mono (by omega)
  · intro x _ _
    trivial
  · intro hz
    simp [GlobalList.one] at hz

noncomputable def switched {G D : Set J} (hG : Described atoms G 24)
    (hD : Described atoms D 1) (hcover : ∀ x ∈ W, x ∉ D → x ∈ G) (k : ℕ) :
    RunData (GlobalList.pair (G ∩ RankTail rank k) D) rank atoms W := by
  refine { base := fun i => if i = 0 then G else D
           threshold := fun i => if i = 0 then k else 0
           second := D
           entry_eq := ?_, simple := ?_, first_small := ?_
           second_small := hD, second_eq := ?_, cover := ?_, pair := ?_ }
  · intro i _
    by_cases he : i = 0
    · simp [GlobalList.pair, he]
    · ext x
      simp [GlobalList.pair, he, RankTail]
  · intro i _ hn
    simpa only [hn, ite_false] using hD.mono (show 1 ≤ 2 by omega)
  · simpa using hG
  · simp
  · simpa using hcover
  · intro _ x _ hx
    exact ⟨by simp [GlobalList.pair], by simpa [GlobalList.pair] using hx⟩

end RunData
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section NumericWalk
variable {J : Type}

def PriorityCut (priority : J → ℕ) (k : ℕ) : Set J := {x | priority x < k}

theorem priorityCut_prefix (W : Finset J) (priority : J → ℕ) (k : ℕ) :
    PrefixOn W priority (PriorityCut priority k) := by
  intro x _ hx y _ hy
  change priority x < k at hx
  change ¬priority y < k at hy
  omega

theorem priorityCut_ideal {W : Finset J} {r : J → J → Prop} {priority : J → ℕ}
    (hstrict : ∀ x ∈ W, ∀ y ∈ W, r x y → priority x < priority y) (k : ℕ) :
    IdealOn W r (PriorityCut priority k) := by
  intro x hx y hy hxy hlow
  exact (hstrict x hx y hy hxy).trans hlow

theorem numeric_shared_cutoff {W : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {s k : ℕ}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed W time) (hpos : AdmissiblePosition W time s)
    (hinj : Set.InjOn priority W)
    (hstrict : ∀ x ∈ W, ∀ y ∈ W, r x y → priority x < priority y)
    (hnorm : LocalObstruction W r time priority)
    (hsep : Separator W r time (PriorityCut priority k) s) :
    ∃ t, s ≤ t ∧ AdvancePath W r time (PriorityCut priority (k+1)) s t ∧
      Separator W r time (PriorityCut priority k) t ∧
      Separator W r time (PriorityCut priority (k+1)) t := by
  classical
  by_cases hex : ∃ x ∈ W, priority x = k
  · obtain ⟨x, hx, hxk⟩ := hex
    apply shared_cutoff (a := x) htrans hrespect hclosed hpos
      (priorityCut_ideal hstrict k) (priorityCut_ideal hstrict (k+1))
      (priorityCut_prefix W priority k) (priorityCut_prefix W priority (k+1)) ?_ hnorm hsep
    intro z hz
    change priority z < k+1 ↔ priority z < k ∨ z = x
    constructor
    · intro h
      by_cases hzk : priority z < k
      · exact Or.inl hzk
      · exact Or.inr (hinj hz hx (by omega))
    · rintro (h | rfl) <;> omega
  · have heq : ∀ z ∈ W, z ∈ PriorityCut priority k ↔ z ∈ PriorityCut priority (k+1) := by
      intro z hz
      have hne : priority z ≠ k := fun h => hex ⟨z, hz, h⟩
      change priority z < k ↔ priority z < k+1
      omega
    exact ⟨s, le_rfl, .refl s, hsep, (separator_congr heq).mp hsep⟩

structure NumericWalkData (E : Finset J) (r : J → J → Prop)
    (time priority : J → ℕ) (a lo count : ℕ) where
  position : Fin (count+1) → ℕ
  first : position 0 = a
  endpoint : ∀ i, position i = a ∨ ∃ x ∈ E, time x = position i
  separator : ∀ i, Separator E r time (PriorityCut priority (lo+i.val)) (position i)
  history : ∀ i, CutoffWalk E r time priority (PriorityCut priority (lo+i.val)) a (position i)
  steps : ∀ i : Fin count,
    AdvancePath E r time (PriorityCut priority (lo+i.val+1))
      (position i.castSucc) (position i.succ) ∧
    Separator E r time (PriorityCut priority (lo+i.val)) (position i.succ)

theorem exists_numeric_walk {E : Finset J} {r : J → J → Prop}
    {time priority : J → ℕ} {a lo : ℕ}
    (htrans : ∀ ⦃u v w⦄, r u v → r v w → r u w)
    (hrespect : ∀ u v, r u v → time u < time v)
    (hclosed : SlotClosed E time) (hpos : AdmissiblePosition E time a)
    (hinj : Set.InjOn priority E)
    (hstrict : ∀ x ∈ E, ∀ y ∈ E, r x y → priority x < priority y)
    (hnorm : LocalObstruction E r time priority)
    (hstart : Separator E r time (PriorityCut priority lo) a) (count : ℕ) :
    Nonempty (NumericWalkData E r time priority a lo count) := by
  classical
  induction count with
  | zero =>
    refine ⟨⟨fun _ => a, rfl, fun _ => Or.inl rfl, ?_, ?_, fun i => Fin.elim0 i⟩⟩
    · intro i
      have he : i.val = 0 := by omega
      simpa only [he, Nat.add_zero] using hstart
    · intro _
      exact .refl
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    let last : Fin (n+1) := Fin.last n
    have hlastpos : AdmissiblePosition E time (ih.position last) := by
      rcases ih.endpoint last with he | hm
      · simpa only [he] using hpos
      · exact Or.inl hm
    obtain ⟨t, _ht, hpath, hsep, hnext⟩ := numeric_shared_cutoff htrans hrespect hclosed
      hlastpos hinj hstrict hnorm (ih.separator last)
    let pos : Fin (n+2) → ℕ := Fin.lastCases t ih.position
    have hcast (i : Fin (n+1)) : pos i.castSucc = ih.position i := by simp [pos]
    have hend : pos (Fin.last (n+1)) = t := by simp [pos]
    refine ⟨{ position := pos, first := ?_, endpoint := ?_, separator := ?_, history := ?_, steps := ?_ }⟩
    · change pos (0 : Fin (n+1)).castSucc = a
      rw [hcast, ih.first]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        rcases hpath.endpoint with he | hm
        · rw [he]
          exact ih.endpoint last
        · exact Or.inr hm
      · rw [hcast]
        exact ih.endpoint j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        simpa only [last, Fin.val_last, Nat.add_assoc] using hnext
      · rw [hcast]
        exact ih.separator j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hend]
        apply CutoffWalk.trans_advance
          ((ih.history last).mono (fun z _ hz => show priority z < lo + (n+1) from by
            have : priority z < lo + n := hz; omega)) hpath
          (priorityCut_ideal hstrict _) (priorityCut_prefix E priority _) (fun _ _ hz => hz)
      · rw [hcast]
        exact ih.history j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change AdvancePath E r time (PriorityCut priority (lo+n+1))
          (pos (Fin.last n).castSucc) (pos (Fin.last (n+1))) ∧ _
        rw [hcast, hend]
        constructor
        · exact hpath
        · simpa only [Fin.succ_last, hend] using hsep
      · have hleft : pos j.castSucc.castSucc = ih.position j.castSucc := hcast _
        have hright : pos j.castSucc.succ = ih.position j.succ := by
          rw [Fin.succ_castSucc, hcast]
        simpa only [Fin.val_castSucc, hleft, hright] using ih.steps j

end NumericWalk
end ThreeMachine.Structure

end

end OAI
