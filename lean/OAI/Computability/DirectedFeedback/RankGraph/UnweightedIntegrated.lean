import Mathlib

namespace OAI

section

namespace DirectedFeedback

def CyclicWalk {V : Type*} (R : V → V → Prop) {n : ℕ}
    (f : Fin (n + 1) → V) : Prop := ∀ i, R (f i) (f (i + 1))

theorem cyclicWalk_contains_cycle {V : Type*} (R : V → V → Prop)
    (n : ℕ) (f : Fin (n + 1) → V) (hf : CyclicWalk R f) :
    ∃ (k : ℕ) (g : Fin (k + 1) → V),
      Function.Injective g ∧ CyclicWalk R g ∧ Set.range g ⊆ Set.range f := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hinj : Function.Injective f
    · exact ⟨n, f, hinj, hf, Set.Subset.rfl⟩
    · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
      have hneval : a.val ≠ b.val := fun h => hne (Fin.ext h)
      have hex : ∃ i j : Fin (n + 1), i.val < j.val ∧ f i = f j := by
        rcases lt_or_gt_of_ne hneval with hlt | hgt
        · exact ⟨a, b, hlt, hab⟩
        · exact ⟨b, a, hgt, hab.symm⟩
      obtain ⟨i, j, hij, heq⟩ := hex
      let k := j.val - i.val - 1
      have hklen : k + 1 = j.val - i.val := by dsimp [k]; omega
      have hkn : k < n := by dsimp [k]; omega
      let idx : Fin (k + 1) → Fin (n + 1) :=
        fun t => ⟨i.val + t.val, by have := t.isLt; have := j.isLt; omega⟩
      let g := f ∘ idx
      have hg : CyclicWalk R g := by
        intro t
        by_cases ht : t.val + 1 < k + 1
        · have hnext : idx (t + 1) = idx t + 1 := by
            apply Fin.ext
            have hsmall : (idx t).val + 1 < n + 1 := by
              dsimp [idx]; have := j.isLt; omega
            change i.val + (t + 1).val = (idx t + 1).val
            rw [Fin.val_add_one_of_lt' ht, Fin.val_add_one_of_lt' hsmall]
            dsimp [idx]
            omega
          simpa only [g, Function.comp_apply, hnext] using hf (idx t)
        · have htlast : t.val = k := by omega
          have hwrap : t + 1 = 0 := by
            apply Fin.ext
            simp [Fin.val_add, htlast]
          have hnext : idx t + 1 = j := by
            apply Fin.ext
            have hsmall : (idx t).val + 1 < n + 1 := by
              dsimp [idx]; have := j.isLt; omega
            rw [Fin.val_add_one_of_lt' hsmall]
            dsimp [idx]
            omega
          have hzero : idx 0 = i := by ext; simp [idx]
          dsimp [g]
          rw [hwrap, hzero, heq]
          simpa only [hnext] using hf (idx t)
      obtain ⟨q, c, hcinj, hc, hcrange⟩ := ih k hkn g hg
      refine ⟨q, c, hcinj, hc, ?_⟩
      rintro v ⟨t, rfl⟩
      obtain ⟨u, hu⟩ := hcrange ⟨t, rfl⟩
      exact ⟨idx u, hu⟩

def FeedbackR {V : Type*} (R : V → V → Prop) (F : Finset V) : Prop :=
  ∀ (n : ℕ) (f : Fin (n + 1) → V),
    Function.Injective f → CyclicWalk R f → ∃ i, f i ∈ F

theorem feedback_hits_walk {V : Type*} (R : V → V → Prop) (F : Finset V)
    (hF : FeedbackR R F) (n : ℕ) (f : Fin (n + 1) → V)
    (hf : CyclicWalk R f) : ∃ i, f i ∈ F := by
  obtain ⟨k, g, hginj, hg, hsub⟩ := cyclicWalk_contains_cycle R n f hf
  obtain ⟨i, hi⟩ := hF k g hginj hg
  obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
  exact ⟨j, hj ▸ hi⟩

abbrev Clone {V : Type*} (c : V → ℕ) := (v : V) × Fin (c v)

def cloneRel {V : Type*} (R : V → V → Prop) (c : V → ℕ) :
    Clone c → Clone c → Prop := fun u v => R u.1 v.1

def cloneSet {V : Type*} [DecidableEq V] (c : V → ℕ) (F : Finset V) :
    Finset (Clone c) := F.sigma (fun _v => Finset.univ)

@[simp] theorem mem_cloneSet {V : Type*} [DecidableEq V]
    (c : V → ℕ) (F : Finset V) (z : Clone c) : z ∈ cloneSet c F ↔ z.1 ∈ F := by
  simp [cloneSet]

@[simp] theorem card_cloneSet {V : Type*} [DecidableEq V]
    (c : V → ℕ) (F : Finset V) : (cloneSet c F).card = ∑ v ∈ F, c v := by
  simp [cloneSet, Finset.card_sigma]

def fullClusters {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (Q : Finset (Clone c)) : Finset V :=
  Finset.univ.filter (fun v => ∀ j : Fin (c v), Sigma.mk v j ∈ Q)

@[simp] theorem mem_fullClusters {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (Q : Finset (Clone c)) (v : V) :
    v ∈ fullClusters c Q ↔ ∀ j : Fin (c v), Sigma.mk v j ∈ Q := by
  simp [fullClusters]

theorem cloneSet_feedback {V : Type*} [DecidableEq V] (R : V → V → Prop)
    (c : V → ℕ) (F : Finset V) (hF : FeedbackR R F) :
    FeedbackR (cloneRel R c) (cloneSet c F) := by
  intro n f _ hf
  obtain ⟨i, hi⟩ := feedback_hits_walk R F hF n (fun i => (f i).1) hf
  exact ⟨i, (mem_cloneSet c F (f i)).mpr hi⟩

theorem fullClusters_feedback {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (c : V → ℕ) (Q : Finset (Clone c))
    (hQ : FeedbackR (cloneRel R c) Q) : FeedbackR R (fullClusters c Q) := by
  classical
  intro n f hinj hf
  by_contra hnone
  have hex (i : Fin (n + 1)) : ∃ j : Fin (c (f i)), Sigma.mk (f i) j ∉ Q := by
    have hi : f i ∉ fullClusters c Q := fun h => hnone ⟨i, h⟩
    simpa only [mem_fullClusters, not_forall] using hi
  choose j hj using hex
  let g : Fin (n + 1) → Clone c := fun i => ⟨f i, j i⟩
  have hginj : Function.Injective g := by
    intro i k h
    apply hinj
    exact congrArg Sigma.fst h
  obtain ⟨i, hi⟩ := hQ n g hginj hf
  exact hj i hi

theorem cloneSet_fullClusters_subset {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (Q : Finset (Clone c)) : cloneSet c (fullClusters c Q) ⊆ Q := by
  intro z hz
  exact (mem_fullClusters c Q z.1).mp ((mem_cloneSet c _ z).mp hz) z.2

theorem fullClusters_cost_le {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (Q : Finset (Clone c)) : ∑ v ∈ fullClusters c Q, c v ≤ Q.card := by
  rw [← card_cloneSet]
  exact Finset.card_le_card (cloneSet_fullClusters_subset c Q)

theorem clone_feedback_iff {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (c : V → ℕ) (k : ℕ) :
    (∃ Q : Finset (Clone c), FeedbackR (cloneRel R c) Q ∧ Q.card ≤ k) ↔
      ∃ F : Finset V, FeedbackR R F ∧ (∑ v ∈ F, c v) ≤ k := by
  constructor
  · rintro ⟨Q, hQ, hk⟩
    exact ⟨fullClusters c Q, fullClusters_feedback R c Q hQ,
      (fullClusters_cost_le c Q).trans hk⟩
  · rintro ⟨F, hF, hk⟩
    exact ⟨cloneSet c F, cloneSet_feedback R c F hF, by simpa using hk⟩

def roundCopies {V : Type*} (S : ℕ) (w : V → ℚ) (v : V) : ℕ := ⌈(S : ℚ) * w v⌉₊

theorem roundCopies_pos {V : Type*} (S : ℕ) (hS : 0 < S)
    (w : V → ℚ) (hw : ∀ v, 0 < w v) (v : V) : 0 < roundCopies S w v := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (Nat.cast_pos.mpr hS) (hw v)

theorem weighted_cost_le_copies {V : Type*} [DecidableEq V]
    (S : ℕ) (w : V → ℚ) (F : Finset V) :
    (S : ℚ) * (∑ v ∈ F, w v) ≤ (∑ v ∈ F, roundCopies S w v : ℕ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact Nat.le_ceil _

theorem copies_cost_le {V : Type*} [DecidableEq V]
    (S : ℕ) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (F : Finset V) :
    (∑ v ∈ F, roundCopies S w v : ℕ) ≤ (S : ℚ) * (∑ v ∈ F, w v) + F.card := by
  rw [Nat.cast_sum, Finset.mul_sum]
  calc
    _ ≤ ∑ v ∈ F, ((S : ℚ) * w v + 1) := by
      apply Finset.sum_le_sum
      intro v _
      exact (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (hw v))).le
    _ = _ := by simp [Finset.sum_add_distrib]

theorem rounded_clone_completeness {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (F : Finset V) (hF : FeedbackR R F) (a : ℚ) (hcost : (∑ v ∈ F, w v) ≤ a) :
    ∃ Q : Finset (Clone (roundCopies (Fintype.card V) w)),
      FeedbackR (cloneRel R (roundCopies (Fintype.card V) w)) Q ∧
        (Q.card : ℚ) ≤ Fintype.card V * (a + 1) := by
  refine ⟨cloneSet _ F, cloneSet_feedback R _ F hF, ?_⟩
  rw [card_cloneSet]
  have hbound := copies_cost_le (Fintype.card V) w hw F
  have hcard : (F.card : ℚ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ F
  have hscaled := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg (Fintype.card V) :
      (0 : ℚ) ≤ Fintype.card V)
  nlinarith

theorem rounded_clone_soundness {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (w : V → ℚ) (S : ℕ) (hS : 0 < S)
    (b : ℚ) (hcost : ∀ F : Finset V, FeedbackR R F → b < ∑ v ∈ F, w v)
    (Q : Finset (Clone (roundCopies S w)))
    (hQ : FeedbackR (cloneRel R (roundCopies S w)) Q) :
    (S : ℚ) * b < Q.card := by
  have hF := fullClusters_feedback R (roundCopies S w) Q hQ
  have hlt := mul_lt_mul_of_pos_left (hcost _ hF) (Nat.cast_pos.mpr hS : (0 : ℚ) < S)
  have hround := weighted_cost_le_copies S w (fullClusters (roundCopies S w) Q)
  have hcard : (∑ v ∈ fullClusters (roundCopies S w) Q, roundCopies S w v : ℕ) ≤
      (Q.card : ℚ) := by exact_mod_cast fullClusters_cost_le (roundCopies S w) Q
  exact hlt.trans_le (hround.trans hcard)

theorem rounded_clone_size {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) (C : ℚ) (hC : ∀ v, w v ≤ C) :
    (Fintype.card (Clone (roundCopies (Fintype.card V) w)) : ℚ) ≤
      C * (Fintype.card V : ℚ) ^ 2 + Fintype.card V := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hbound := copies_cost_le (Fintype.card V) w hw Finset.univ
  have hwtotal : (∑ v, w v) ≤ Fintype.card V * C := by
    calc
      _ ≤ ∑ _v : V, C := Finset.sum_le_sum (fun v _ => hC v)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hwtotal
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℚ) ≤ Fintype.card V)
  simp only [Finset.card_univ] at hbound
  nlinarith

end DirectedFeedback

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.RankGraph

variable (U V X Y : Type) (T N : ℕ)

abbrev Tuple := (Σ t : Fin (T + 1), Fin t.val → U) ⊕
  (Σ t : Fin T, (Fin t.val → U) × V)

abbrev Domain : Tuple U V T → Type
  | .inl ⟨t, _⟩ => Fin t.val → X
  | .inr ⟨t, _⟩ => (Fin t.val → X) × Y

instance [Fintype X] [Fintype Y] (d : Tuple U V T) : Fintype (Domain U V X Y T d) := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Fintype (Fin t.val → X))
  | inr d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Fintype ((Fin t.val → X) × Y))

instance [Nonempty X] [Nonempty Y] (d : Tuple U V T) : Nonempty (Domain U V X Y T d) := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Nonempty (Fin t.val → X))
  | inr d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Nonempty ((Fin t.val → X) × Y))

abbrev Formal := Σ d : Tuple U V T, Domain U V X Y T d → Fin N

inductive PrefixStep : Formal U V X Y T N → Formal U V X Y T N → Prop
  | big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
      (x : (Fin t → X) → Fin N) :
      PrefixStep
        ⟨.inl ⟨⟨t, by omega⟩, Fin.init s⟩, x⟩
        ⟨.inl ⟨⟨t + 1, by omega⟩, s⟩, fun a => x (Fin.init a)⟩
  | small (t : Fin T) (s : Fin t.val → U) (v : V)
      (x : (Fin t.val → X) → Fin N) :
      PrefixStep
        ⟨.inl ⟨⟨t.val, by omega⟩, s⟩, x⟩
        ⟨.inr ⟨t, s, v⟩, fun a => x a.1⟩

abbrev Rank := Quot (PrefixStep U V X Y T N)

instance [Finite U] [Finite V] [Finite X] [Finite Y] : Finite (Rank U V X Y T N) := by
  let := Fintype.ofFinite U
  let := Fintype.ofFinite V
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  exact Quot.finite _

variable {U V X Y T N}

def vertex (d : Tuple U V T) (x : Domain U V X Y T d → Fin N) : Rank U V X Y T N :=
  Quot.mk _ ⟨d, x⟩

def labels (ellU : U → X) (ellV : V → Y) :
    (d : Tuple U V T) → Domain U V X Y T d
  | .inl ⟨_, s⟩ => fun i => ellU (s i)
  | .inr ⟨_, s, v⟩ => (fun i => ellU (s i), ellV v)

def eval (ellU : U → X) (ellV : V → Y) : Rank U V X Y T N → Fin N :=
  Quot.lift (fun z => z.2 (labels ellU ellV z.1)) (by
    intro a b hab
    cases hab <;> rfl)

@[simp] theorem eval_vertex (ellU : U → X) (ellV : V → Y)
    (d : Tuple U V T) (x : Domain U V X Y T d → Fin N) :
    eval ellU ellV (vertex d x) = x (labels ellU ellV d) := rfl

def Arc (a b : Rank U V X Y T N) : Prop :=
  ∃ (d : Tuple U V T) (x y : Domain U V X Y T d → Fin N),
    a = vertex d x ∧ b = vertex d y ∧ ∀ lambda, x lambda < y lambda

theorem eval_arc (ellU : U → X) (ellV : V → Y)
    {a b : Rank U V X Y T N} (h : Arc a b) : eval ellU ellV a < eval ellU ellV b := by
  obtain ⟨d, x, y, rfl, rfl, h⟩ := h
  exact h (labels ellU ellV d)

theorem arc_irrefl [Nonempty X] [Nonempty Y] (a : Rank U V X Y T N) : ¬Arc a a := by
  intro h
  exact (lt_irrefl _) (eval_arc (fun _ => Classical.choice ‹Nonempty X›)
    (fun _ => Classical.choice ‹Nonempty Y›) h)

def emptyTuple : Tuple U V T := .inl ⟨⟨0, Nat.zero_lt_succ _⟩, Fin.elim0⟩

def marker (j : Fin N) : Rank U V X Y T N := vertex emptyTuple (fun _ => j)

@[simp] theorem eval_marker (ellU : U → X) (ellV : V → Y) (j : Fin N) :
    eval ellU ellV (marker j : Rank U V X Y T N) = j := rfl

theorem marker_injective [Nonempty X] [Nonempty Y] :
    Function.Injective (marker : Fin N → Rank U V X Y T N) := by
  intro a b h
  simpa using congrArg (eval (fun _ => Classical.choice ‹Nonempty X›)
    (fun _ => Classical.choice ‹Nonempty Y›)) h

theorem marker_arc {i j : Fin N} (h : i < j) :
    Arc (marker i : Rank U V X Y T N) (marker j) :=
  ⟨emptyTuple, (fun _ => i), (fun _ => j), rfl, rfl, fun _ => h⟩

theorem prefix_big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
    (x : (Fin t → X) → Fin N) :
    (vertex (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) x : Rank U V X Y T N) =
      vertex (.inl ⟨⟨t + 1, by omega⟩, s⟩) (fun a => x (Fin.init a)) :=
  Quot.sound (.big t ht s x)

theorem prefix_small (t : Fin T) (s : Fin t.val → U) (v : V)
    (x : (Fin t.val → X) → Fin N) :
    (vertex (.inl ⟨⟨t.val, by omega⟩, s⟩) x : Rank U V X Y T N) =
      vertex (.inr ⟨t, s, v⟩) (fun a => x a.1) :=
  Quot.sound (.small t s v x)

theorem constant_pure (t : ℕ) (ht : t ≤ T) (s : Fin t → U) (j : Fin N) :
    (vertex (.inl ⟨⟨t, by omega⟩, s⟩) (fun _ => j) : Rank U V X Y T N) = marker j := by
  induction t with
  | zero =>
      have hs : s = Fin.elim0 := funext (fun i => Fin.elim0 i)
      subst s
      rfl
  | succ t ih =>
      rw [← prefix_big t (by omega) s (fun _ => j)]
      exact ih (by omega) (Fin.init s)

theorem constant_vertex (d : Tuple U V T) (j : Fin N) :
    (vertex d (fun _ => j) : Rank U V X Y T N) = marker j := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact constant_pure t.val (by omega) s j
  | inr d =>
      rcases d with ⟨t, s, v⟩
      rw [← prefix_small t s v (fun _ => j)]
      exact constant_pure t.val (by omega) s j

end DirectedFeedback.RankGraph

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L : ℕ}
variable (ord : Rank U V X Y T N → ℕ)
variable (ψ : Fin L → Fin N)

def twoLevel (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a h : Fin L) : Rank U V X Y T N := by
  classical
  exact vertex d (fun lambda => if lambda ∈ E then ψ a else ψ h)

def compareBit (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a c h : Fin L) : Bool :=
  decide (ord (twoLevel ψ d E a h) < ord (marker (ψ c)))

def usable (a c h : Fin L) : Prop :=
  1 ≤ a.val ∧ a < c ∧ 4 ≤ c.val ∧ c.val + 6 ≤ L ∧ c.val + 2 ≤ h.val

def referenceBit (hL : 30 ≤ L) (d : Tuple U V T)
    (E : Set (Domain U V X Y T d)) : Bool :=
  compareBit ord ψ d E ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨L - 2, by omega⟩

def Good (hL : 30 ≤ L) (d : Tuple U V T) : Prop :=
  ∀ E a c h, usable a c h → compareBit ord ψ d E a c h = referenceBit ord ψ hL d E

variable {ord ψ}

theorem twoLevel_arc (hψ : StrictMono ψ) (d : Tuple U V T)
    {E E' : Set (Domain U V X Y T d)} (hsub : E ⊆ E')
    {a a' h h' : Fin L} (haa : a < a') (hah : a < h') (hhh : h < h') :
    Arc (twoLevel ψ d E' a h) (twoLevel ψ d E a' h') := by
  classical
  refine ⟨d, _, _, rfl, rfl, ?_⟩
  intro lambda
  by_cases he : lambda ∈ E
  · simp only [he, hsub he, ↓reduceIte]
    exact hψ haa
  · by_cases he' : lambda ∈ E'
    · simp only [he, he', ↓reduceIte]
      exact hψ hah
    · simp only [he, he', ↓reduceIte]
      exact hψ hhh

theorem compareBit_mono_of_arc
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    {d : Tuple U V T} {E E' : Set (Domain U V X Y T d)}
    {a a' c h h' : Fin L}
    (ha : Arc (twoLevel ψ d E' a h) (twoLevel ψ d E a' h')) :
    compareBit ord ψ d E a' c h' ≤ compareBit ord ψ d E' a c h := by
  rw [Bool.le_iff_imp]
  simp only [compareBit, decide_eq_true_eq]
  exact fun hh => (hord ha).trans hh

theorem good_monotone (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (d : Tuple U V T) (hg : Good ord ψ hL d) :
    Monotone (referenceBit ord ψ hL d) := by
  intro E E' hsub
  have h1 := hg E' ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨16, by omega⟩
    (by unfold usable; simp; omega)
  have h2 := hg E ⟨2, by omega⟩ ⟨14, by omega⟩ ⟨17, by omega⟩
    (by unfold usable; simp; omega)
  rw [← h1, ← h2]
  apply compareBit_mono_of_arc hord
  exact twoLevel_arc hψ d hsub (by simp) (by simp) (by simp)

@[simp] theorem reference_empty (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    referenceBit ord ψ hL d ∅ = false := by
  classical
  have hx : twoLevel (X := X) (Y := Y) ψ d ∅ (⟨1, by omega⟩ : Fin L) ⟨L - 2, by omega⟩ =
      marker (ψ ⟨L - 2, by omega⟩) := by
    simpa [twoLevel] using constant_vertex (X := X) (Y := Y) d (ψ ⟨L - 2, by omega⟩)
  have hlt := hord (marker_arc (U := U) (V := V) (X := X) (Y := Y) (T := T)
    (hψ (show (⟨14, by omega⟩ : Fin L) < ⟨L - 2, by omega⟩ from by simp; omega)))
  simp only [referenceBit, compareBit, hx, decide_eq_false_iff_not]
  exact not_lt_of_gt hlt

@[simp] theorem reference_univ (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    referenceBit ord ψ hL d Set.univ = true := by
  classical
  have hx : twoLevel (X := X) (Y := Y) ψ d Set.univ (⟨1, by omega⟩ : Fin L) ⟨L - 2, by omega⟩ =
      marker (ψ ⟨1, by omega⟩) := by
    simpa [twoLevel] using constant_vertex (X := X) (Y := Y) d (ψ ⟨1, by omega⟩)
  simp only [referenceBit, compareBit, hx, decide_eq_true_eq]
  exact hord (marker_arc (hψ (by simp)))

theorem compare_prefix_big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
    (E : Set (Fin t → X)) (a c h : Fin L) :
    compareBit ord ψ (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) E a c h =
      compareBit ord ψ (.inl ⟨⟨t + 1, by omega⟩, s⟩) (Fin.init ⁻¹' E) a c h := by
  unfold compareBit twoLevel
  rw [prefix_big t ht s]
  rfl

theorem compare_prefix_small (t : Fin T) (s : Fin t.val → U) (v : V)
    (E : Set (Fin t.val → X)) (a c h : Fin L) :
    compareBit ord ψ (.inl ⟨⟨t.val, by omega⟩, s⟩) E a c h =
      compareBit ord ψ (.inr ⟨t, s, v⟩) (Prod.fst ⁻¹' E) a c h := by
  unfold compareBit twoLevel
  rw [prefix_small t s v]
  rfl

theorem good_prefix_big (hL : 30 ≤ L) (t : ℕ) (ht : t < T)
    (s : Fin (t + 1) → U) (hg : Good ord ψ hL (.inl ⟨⟨t + 1, by omega⟩, s⟩)) :
    Good ord ψ hL (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) := by
  intro E a c h hu
  unfold referenceBit
  rw [compare_prefix_big t ht s, compare_prefix_big t ht s]
  exact hg _ _ _ _ hu

theorem good_prefix_small (hL : 30 ≤ L) (t : Fin T) (s : Fin t.val → U) (v : V)
    (hg : Good ord ψ hL (.inr ⟨t, s, v⟩)) :
    Good ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩) := by
  intro E a c h hu
  unfold referenceBit
  rw [compare_prefix_small t s v, compare_prefix_small t s v]
  exact hg _ _ _ _ hu

end DirectedFeedback.RankGraph

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L k K : ℕ}
variable (ψ : Fin L → Fin N) (d : Tuple U V T)

def belowWildcard (cell : Domain U V X Y T d → Fin k)
    (Z : Set (Domain U V X Y T d)) (level : Fin k → Fin N)
    (x : Domain U V X Y T d → Fin N) : Prop :=
  ∀ lambda, lambda ∉ Z → x lambda < level (cell lambda)

def aboveWildcard (cell : Domain U V X Y T d → Fin k)
    (Z : Set (Domain U V X Y T d)) (level : Fin k → Fin N)
    (x : Domain U V X Y T d → Fin N) : Prop :=
  ∀ lambda, lambda ∉ Z → level (cell lambda) < x lambda

variable {ψ d}

theorem wildcard_forcing (hL : L = 10 * K + 30) (hk : k ≤ K)
    (hψ : StrictMono ψ) (ord : Rank U V X Y T N → ℕ)
    (hg : Good ord ψ (by omega) d)
    (cell : Domain U V X Y T d → Fin k) (Z : Set (Domain U V X Y T d))
    (cut : ℕ) (hcut : cut ≤ k)
    (hpath : ∀ x y, belowWildcard d cell Z
        (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) x →
      aboveWildcard d cell Z
        (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) y →
      ord (vertex d x) < ord (vertex d y)) :
    ¬(referenceBit ord ψ (by omega) d ({lambda | (cell lambda).val < cut} \ Z) = false ∧
      referenceBit ord ψ (by omega) d
        (({lambda | (cell lambda).val < cut} \ Z) ∪ Z) = true) := by
  classical
  let E : Set (Domain U V X Y T d) := {lambda | (cell lambda).val < cut} \ Z
  let c : Fin L := ⟨10 * cut + 14, by omega⟩
  let lo : Fin L := ⟨1, by omega⟩
  let hi : Fin L := ⟨L - 2, by omega⟩
  let cm : Fin L := ⟨10 * cut + 12, by omega⟩
  let cp : Fin L := ⟨10 * cut + 16, by omega⟩
  let x : Domain U V X Y T d → Fin N := fun a => @ite (Fin N) (a ∈ E) (Classical.propDecidable _) (ψ lo) (ψ cp)
  let y : Domain U V X Y T d → Fin N := fun a => @ite (Fin N) (a ∈ E ∪ Z) (Classical.propDecidable _) (ψ cm) (ψ hi)
  have hx : belowWildcard d cell Z
      (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) x := by
    intro a ha
    by_cases hc : (cell a).val < cut
    · simp only [x, E, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha, not_false_eq_true,
        and_self, ↓reduceIte]
      apply hψ
      change 1 < 10 * (cell a).val + 19
      omega
    · simp only [x, E, Set.mem_sdiff, Set.mem_ofPred_eq, hc, false_and, ↓reduceIte]
      apply hψ
      change 10 * cut + 16 < 10 * (cell a).val + 19
      omega
  have hy : aboveWildcard d cell Z
      (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) y := by
    intro a ha
    by_cases hc : (cell a).val < cut
    · simp only [y, E, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha,
        not_false_eq_true, and_self, or_false, ↓reduceIte]
      apply hψ
      change 10 * (cell a).val + 19 < 10 * cut + 12
      omega
    · simp only [y, E, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha,
        false_and, or_self, ↓reduceIte]
      apply hψ
      change 10 * (cell a).val + 19 < L - 2
      have := (cell a).isLt
      omega
  have hu1 : usable lo c cp := by unfold usable; simp [lo, c, cp]; omega
  have hu2 : usable cm c hi := by unfold usable; simp [cm, c, hi]; omega
  intro hh
  have hb0 := (hg E lo c cp hu1).trans hh.1
  have hb1 := (hg (E ∪ Z) cm c hi hu2).trans hh.2
  have hn : ¬ord (vertex d x) < ord (marker (ψ c)) := by
    unfold compareBit at hb0
    have hh0 := of_decide_eq_false hb0
    simpa only [twoLevel, x] using hh0
  have hp : ord (vertex d y) < ord (marker (ψ c)) := by
    unfold compareBit at hb1
    have hh1 := of_decide_eq_true hb1
    simpa only [twoLevel, y] using hh1
  exact hn ((hpath x y hx hy).trans hp)

theorem comparison_forcing (hL : 30 ≤ L)
    (ord : Rank U V X Y T N → ℕ) (a b : Tuple U V T)
    (ha : Good ord ψ hL a) (hb : Good ord ψ hL b)
    (Ea : Set (Domain U V X Y T a)) (Eb : Set (Domain U V X Y T b))
    (hpath : ord (twoLevel ψ b Eb ⟨1, by omega⟩ ⟨16, by omega⟩) <
      ord (twoLevel ψ a Ea ⟨2, by omega⟩ ⟨17, by omega⟩)) :
    ¬(referenceBit ord ψ hL a Ea = true ∧ referenceBit ord ψ hL b Eb = false) := by
  intro hh
  have hh0 := (hb Eb ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨16, by omega⟩
    (by unfold usable; simp; omega)).trans hh.2
  have hh1 := (ha Ea ⟨2, by omega⟩ ⟨14, by omega⟩ ⟨17, by omega⟩
    (by unfold usable; simp; omega)).trans hh.1
  simp only [compareBit, decide_eq_false_iff_not] at hh0
  simp only [compareBit, decide_eq_true_eq] at hh1
  exact hh0 (hpath.trans hh1)

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.TestGraph
open RankGraph
variable {U V X Y W C : Type} {T N : ℕ}

structure Wildcard where
  tuple : Tuple U V T
  cells : ℕ
  cell : Domain U V X Y T tuple → Fin cells
  stars : Set (Domain U V X Y T tuple)
  level : Fin cells → Fin N

structure Comparison where
  source : Rank U V X Y T N
  target : Rank U V X Y T N

abbrev Vertex (U V X Y W C : Type) (T N : ℕ) := Rank U V X Y T N ⊕ (W ⊕ C)

inductive Arc (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N)) :
    Vertex U V X Y W C T N → Vertex U V X Y W C T N → Prop
  | rank {a b} (h : RankGraph.Arc a b) : Arc wild comp (.inl a) (.inl b)
  | wild_in (w : W) (x : Domain U V X Y T (wild w).tuple → Fin N)
      (h : belowWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x) :
      Arc wild comp (.inl (vertex (wild w).tuple x)) (.inr (.inl w))
  | wild_out (w : W) (x : Domain U V X Y T (wild w).tuple → Fin N)
      (h : aboveWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x) :
      Arc wild comp (.inr (.inl w)) (.inl (vertex (wild w).tuple x))
  | comp_in (c : C) : Arc wild comp (.inl (comp c).source) (.inr (.inr c))
  | comp_out (c : C) : Arc wild comp (.inr (.inr c)) (.inl (comp c).target)

variable (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))

theorem arc_irrefl [Nonempty X] [Nonempty Y] (a : Vertex U V X Y W C T N) :
    ¬Arc wild comp a a := by
  intro h
  cases h with
  | rank h => exact RankGraph.arc_irrefl _ h

def LabelDeleted (ellU : U → X) (ellV : V → Y) : Vertex U V X Y W C T N → Prop
  | .inl _ => False
  | .inr (.inl w) => labels ellU ellV (wild w).tuple ∈ (wild w).stars
  | .inr (.inr c) => eval ellU ellV (comp c).target ≤ eval ellU ellV (comp c).source

def labelPotential (ellU : U → X) (ellV : V → Y) : Vertex U V X Y W C T N → ℚ
  | .inl r => (eval ellU ellV r).val
  | .inr (.inl w) => ((wild w).level ((wild w).cell (labels ellU ellV (wild w).tuple))).val
  | .inr (.inr c) => ((eval ellU ellV (comp c).source).val +
      (eval ellU ellV (comp c).target).val : ℚ) / 2

theorem labelPotential_increases (ellU : U → X) (ellV : V → Y)
    {a b : Vertex U V X Y W C T N} (hab : Arc wild comp a b)
    (ha : ¬LabelDeleted wild comp ellU ellV a) (hb : ¬LabelDeleted wild comp ellU ellV b) :
    labelPotential wild comp ellU ellV a < labelPotential wild comp ellU ellV b := by
  cases hab with
  | rank h =>
      dsimp [labelPotential]
      exact_mod_cast (eval_arc ellU ellV h : (eval ellU ellV _).val < (eval ellU ellV _).val)
  | wild_in w x h =>
      dsimp [labelPotential, eval_vertex]
      exact_mod_cast (h _ hb : (x _).val < ((wild w).level _).val)
  | wild_out w x h =>
      dsimp [labelPotential, eval_vertex]
      exact_mod_cast (h _ ha : ((wild w).level _).val < (x _).val)
  | comp_in c =>
      have hh : (eval ellU ellV (comp c).source).val < (eval ellU ellV (comp c).target).val :=
        not_le.mp hb
      dsimp [labelPotential]
      have hh' : ((eval ellU ellV (comp c).source).val : ℚ) < (eval ellU ellV (comp c).target).val :=
        by exact_mod_cast hh
      linarith
  | comp_out c =>
      have hh : (eval ellU ellV (comp c).source).val < (eval ellU ellV (comp c).target).val :=
        not_le.mp ha
      dsimp [labelPotential]
      have hh' : ((eval ellU ellV (comp c).source).val : ℚ) < (eval ellU ellV (comp c).target).val :=
        by exact_mod_cast hh
      linarith

theorem labelDeleted_feedback [Fintype U] [Fintype V] [Fintype X] [Fintype Y]
    [Fintype W] [Fintype C] (ellU : U → X) (ellV : V → Y) :
    letI := Fintype.ofFinite (Rank U V X Y T N)
    FeedbackR (Arc wild comp) (Finset.univ.filter (LabelDeleted wild comp ellU ellV)) := by
  let := Fintype.ofFinite (Rank U V X Y T N)
  intro n f _ hf
  by_contra hn
  have hnot (i) : ¬LabelDeleted wild comp ellU ellV (f i) := by
    intro h
    exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hh (i) := labelPotential_increases wild comp ellU ellV (hf i) (hnot i) (hnot (i + 1))
  have hsum := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    Finset.univ_nonempty (fun i _ => hh i)
  have heq : (∑ i : Fin (n + 1), labelPotential wild comp ellU ellV (f (i + 1))) =
      ∑ i : Fin (n + 1), labelPotential wild comp ellU ellV (f i) := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin (n + 1))) _ _ (fun _ => rfl)
  rw [heq] at hsum
  exact (lt_irrefl _) hsum

theorem wildcard_path (ord : Vertex U V X Y W C T N → ℕ)
    (retained : Vertex U V X Y W C T N → Prop)
    (hord : ∀ {a b}, retained a → retained b → Arc wild comp a b → ord a < ord b)
    (hrank : ∀ r, retained (.inl r)) (w : W) (hw : retained (.inr (.inl w)))
    (x y : Domain U V X Y T (wild w).tuple → Fin N)
    (hx : belowWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x)
    (hy : aboveWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level y) :
    ord (.inl (vertex (wild w).tuple x)) < ord (.inl (vertex (wild w).tuple y)) :=
  (hord (hrank _) hw (.wild_in w x hx)).trans (hord hw (hrank _) (.wild_out w y hy))

theorem comparison_path (ord : Vertex U V X Y W C T N → ℕ)
    (retained : Vertex U V X Y W C T N → Prop)
    (hord : ∀ {a b}, retained a → retained b → Arc wild comp a b → ord a < ord b)
    (hrank : ∀ r, retained (.inl r)) (c : C) (hc : retained (.inr (.inr c))) :
    ord (.inl (comp c).source) < ord (.inl (comp c).target) :=
  (hord (hrank _) hc (.comp_in c)).trans (hord hc (hrank _) (.comp_out c))

end DirectedFeedback.TestGraph

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

def boundary (cell : S → Fin k) (r : ℕ) : Set S := {a | (cell a).val < r}

def Transition (g : Set S → Bool) (cell : S → Fin k) (r : Fin k) : Prop :=
  g (boundary cell r.val) = false ∧ g (boundary cell (r.val + 1)) = true

theorem boundary_mono (cell : S → Fin k) : Monotone (boundary cell) :=
  fun _ _ h _ ha => lt_of_lt_of_le ha h

@[simp] theorem boundary_zero (cell : S → Fin k) : boundary cell 0 = ∅ := by
  ext a; simp [boundary]

@[simp] theorem boundary_top (cell : S → Fin k) : boundary cell k = Set.univ := by
  ext a; simp [boundary]

theorem exists_transition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) :
    ∃ r, Transition g cell r := by
  have he : ∃ r : ℕ, g (boundary cell r) = true := ⟨k, by simpa using h1⟩
  let n := Nat.find he
  have hn : g (boundary cell n) = true := Nat.find_spec he
  have hnk : n ≤ k := Nat.find_min' he (by simpa using h1)
  have hnpos : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    simp [hn0, h0] at hn
  refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
  · have hh := Nat.find_min he (show n - 1 < n by omega)
    exact Bool.eq_false_iff.mpr hh
  · simpa only [Nat.sub_add_cancel hnpos] using hn

theorem transition_unique (g : Set S → Bool) (hg : Monotone g) (cell : S → Fin k)
    {a b : Fin k} (ha : Transition g cell a) (hb : Transition g cell b) : a = b := by
  apply le_antisymm
  · by_contra hn
    have hba : b.val + 1 ≤ a.val := by omega
    have hh := hg (boundary_mono cell hba)
    simp only [hb.2, ha.1] at hh
    contradiction
  · by_contra hn
    have hab : a.val + 1 ≤ b.val := by omega
    have hh := hg (boundary_mono cell hab)
    simp only [ha.2, hb.1] at hh
    contradiction

def transition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) : Fin k :=
  Classical.choose (exists_transition g cell h0 h1)

theorem transition_spec (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) :
    Transition g cell (transition g cell h0 h1) :=
  Classical.choose_spec (exists_transition g cell h0 h1)

theorem transition_cell_nonempty (g : Set S → Bool) (cell : S → Fin k)
    {r : Fin k} (hr : Transition g cell r) : ∃ a, cell a = r := by
  by_contra hn
  have he : boundary cell r.val = boundary cell (r.val + 1) := by
    ext a
    have hh : cell a ≠ r := fun h => hn ⟨a, h⟩
    have hh' : (cell a).val ≠ r.val := fun h => hh (Fin.ext h)
    simp only [boundary, Set.mem_ofPred_eq]
    omega
  have hh := hr.1
  rw [he, hr.2] at hh
  contradiction

def conditionedSet (cell : S → Fin k) (r : Fin k) (R : Set X) : Set (S × X) :=
  {a | (cell a.1).val < r.val ∨ cell a.1 = r ∧ a.2 ∈ R}

theorem conditionedSet_mono (cell : S → Fin k) (r : Fin k) :
    Monotone (conditionedSet (X := X) cell r) := by
  intro A B h a ha
  rcases ha with ha | ⟨ha, hb⟩
  · exact Or.inl ha
  · exact Or.inr ⟨ha, h hb⟩

@[simp] theorem conditionedSet_empty (cell : S → Fin k) (r : Fin k) :
    conditionedSet (X := X) cell r ∅ = Prod.fst ⁻¹' boundary cell r.val := by
  ext a; simp [conditionedSet, boundary]

@[simp] theorem conditionedSet_univ (cell : S → Fin k) (r : Fin k) :
    conditionedSet (X := X) cell r Set.univ = Prod.fst ⁻¹' boundary cell (r.val + 1) := by
  ext a
  simp only [conditionedSet, Set.mem_ofPred_eq, Set.mem_univ, and_true,
    Set.mem_preimage, boundary, Fin.ext_iff]
  omega

theorem conditioned_properties (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E) :
    Monotone (fun R => g' (conditionedSet cell r R)) ∧
      g' (conditionedSet cell r ∅) = false ∧
      g' (conditionedSet cell r Set.univ) = true := by
  exact ⟨hg'.comp (conditionedSet_mono cell r), by simpa only [conditionedSet_empty, hlift] using hr.1,
    by simpa only [conditionedSet_univ, hlift] using hr.2⟩

def refineCell (cell : S → Fin k) (P : Set X) (a : S × X) : Fin (2 * k) := by
  classical
  exact ⟨2 * (cell a.1).val + if a.2 ∈ P then 0 else 1, by
    have := (cell a.1).isLt
    split_ifs <;> omega⟩

theorem refined_even_boundary (cell : S → Fin k) (P : Set X) (r : ℕ) :
    boundary (refineCell cell P) (2 * r) = Prod.fst ⁻¹' boundary cell r := by
  classical
  ext a
  simp only [boundary, Set.mem_ofPred_eq, Set.mem_preimage, refineCell]
  split_ifs <;> omega

theorem refined_middle_boundary (cell : S → Fin k) (P : Set X) (r : Fin k) :
    boundary (refineCell cell P) (2 * r.val + 1) = conditionedSet cell r P := by
  classical
  ext a
  simp only [boundary, Set.mem_ofPred_eq, refineCell, conditionedSet, Fin.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem transition_refines (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (P : Set X)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E)
    {r : Fin k} {r' : Fin (2 * k)} (hr : Transition g cell r)
    (hr' : Transition g' (refineCell cell P) r') :
    r'.val / 2 = r.val := by
  have hlow : 2 * r.val ≤ r'.val := by
    by_contra hn
    have hh := hg' (boundary_mono (refineCell cell P)
      (show r'.val + 1 ≤ 2 * r.val by omega))
    rw [hr'.2, refined_even_boundary, hlift, hr.1] at hh
    contradiction
  have hhigh : r'.val < 2 * (r.val + 1) := by
    by_contra hn
    have hh := hg' (boundary_mono (refineCell cell P)
      (show 2 * (r.val + 1) ≤ r'.val by omega))
    rw [refined_even_boundary, hlift, hr.2, hr'.1] at hh
    contradiction
  omega

end DirectedFeedback.Prefix
end
end
end
end

end OAI
