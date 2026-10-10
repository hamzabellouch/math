import OAI.Computability.BinPacking.PCP.PoweringEnumeration
import OAI.Computability.BinPacking.PCP.PoweringMomentBound
import OAI.Computability.BinPacking.PCP.RawInitialMachineBudget

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end BinPackingGames.Foundations.PCP.PoweringReach

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

theorem opinionAt_honest (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (assignment : V → A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors (honestLabels G t assignment) fallback u.val v =
      assignment u.val := by
  rw [opinionAt_eq_decode]
  exact congrFun (decode_encode (selectors v) (fun u => assignment u.val)) u

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

theorem decoded_modal_near (G : PortGraph V D) (t M m : Nat)
    (selectors : ∀ v, AddressSelector (lazyGraph G) t v)
    (labels : V → PaddedLabel (Bool × D) t A) (fallback : A)
    (hM : 1 ≤ M)
    (hlo : (4 * Fintype.card A * M) ^ 2 - M ≤ m)
    (hhi : m ≤ (4 * Fintype.card A * M) ^ 2 + M) (u : V) :
    1 / (2 * (Fintype.card A : ℝ)) ≤
      iterateOperator (lazyGraph G) m
        (matchFn (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
          selectors labels fallback u) u := by
  exact PoweringLazy.lazy_endpoint_modal_transfer G (Fintype.card A) M m
    Fintype.card_pos hM hlo hhi _
    (matchFn_mem_Icc (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u) u
    (decoded_modal_baseline (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u)

end BinPackingGames.Foundations.PCP.PoweringOpinions

end

namespace BinPackingGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

theorem witness_bad (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    decodedBad G accepts assignment (edgeAt G n w k) = true := h.1

theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

theorem witness_implies_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k)
    (direction : Bool) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) = false := by
  rw [poweredGraph_edgeSatisfied]
  exact witness_implies_path_rejection G accepts n selectors labels fallback assignment w k h

end BinPackingGames.Foundations.PCP.PoweringTest

namespace BinPackingGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

private theorem match_in_tail (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail p h ha)).succ

theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail p h ha)

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

theorem addressIndex_matches (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    wordToBall G t center ((allAddresses d t).get (addressIndex G t center u)) = u := by
  rw [addressIndex_get]
  exact (finitePortSelector G t center).correct u

theorem addressIndex_is_first (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (j : AddressIndex d t)
    (hj : j.val < (addressIndex G t center u).val) :
    (wordToBall G t center ((allAddresses d t).get j)).val ≠ u.val := by
  exact firstIndex_is_first _ _ _ j hj

theorem addressIndex_lt (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (addressIndex G t center u).val < ∑ n : Fin (t + 1), d ^ n.val := by
  rw [← length_allAddresses]
  exact (addressIndex G t center u).isLt

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

theorem walkRows_length (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (walkRows G n w).toList.length = n + 1 := by
  simp

def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end BinPackingGames.Foundations.PCP.PoweringOpinionTables

namespace BinPackingGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases bad (v, d) <;> simp [PoweringMoment.bit]

theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

theorem powered_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) :=
  constraint_rejection_mean_eq_count _ _

theorem path_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) := by
  rw [← rejection_mean_eq_path_mean G accepts n selectors labels]
  exact powered_rejection_mean_eq_count G accepts n selectors labels

theorem powered_density_lower_to_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (hcard : 0 < Fintype.card (Dart V D n)) (ε : ℝ)
    (hlower : ε ≤ SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false))) :
    ε * (Fintype.card (Dart V D n) : ℝ) ≤
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) := by
  rw [path_rejection_mean_eq_count G accepts n selectors labels] at hlower
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).1 hlower

theorem natCard_dart [Finite V] [Finite D] (n : Nat) :
    Nat.card (Dart V D n) = 2 * Nat.card V * Nat.card D ^ (n + 1) := by
  simp [Dart, Walk, Nat.card_prod, Nat.card_fun, Nat.mul_assoc]

theorem fintypeCard_dart [Fintype V] [Fintype D] (n : Nat) :
    Fintype.card (Dart V D n) =
      2 * Fintype.card V * Fintype.card D ^ (n + 1) := by
  simpa only [Nat.card_eq_fintype_card] using (natCard_dart (V := V) (D := D) n)

theorem natCard_poweredAlphabet [Finite D] [Finite A] (n : Nat) :
    Nat.card (PaddedLabel D (n + 1) A) =
      Nat.card A ^ (∑ j : Fin (n + 2), Nat.card D ^ j.val) :=
  PoweringLabels.card_paddedLabel (n + 1)

theorem natCard_finitePortAlphabet [Finite A] (d n : Nat) :
    Nat.card (PaddedLabel (Fin d) (n + 1) A) =
      Nat.card A ^ (PoweringAddresses.allAddresses d (n + 1)).length := by
  rw [PoweringLabels.card_paddedLabel, PoweringAddresses.length_allAddresses]
  simp only [Nat.card_fin]

end BinPackingGames.Foundations.PCP.PoweringCounting

namespace BinPackingGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, PoweringOpinionTables.rowsAccepts_walkRows]

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

theorem table_accepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (dartCount vertices d n)) (a b : Fin (labelCount d n)) :
    GenericGraphTables.acceptsAt (table input n).rows i a b =
      rowAccepts input n (decodeDart vertices d n i) a b := by
  change (GenericGraphTables.semantics (table input n)).accepts i a b = _
  rw [semantics_table]
  exact (rowAccepts_eq input n (decodeDart vertices d n i) a b).symm

theorem table_reverse {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (direction : Bool) (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    GenericGraphTables.reverseAt (table input n).rows (encodeDart vertices d n (direction, w)) =
      encodeDart vertices d n (!direction, w) := by
  change (GenericGraphTables.semantics (table input n)).reverse _ = _
  rw [semantics_table]
  change dartEquiv vertices d n ((mathematicalGraph input n).reverse
      ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, w)))) =
    dartEquiv vertices d n (!direction, w)
  rw [(dartEquiv vertices d n).symm_apply_apply]
  rfl

def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end BinPackingGames.Foundations.PCP.PoweringTables

namespace BinPackingGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  simpa using!
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

theorem edgeSatisfied_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (i : Fin (dartCount vertices d n)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels i =
      (mathematicalGraph input n).edgeSatisfied (decodeLabeling d n labels)
        (decodeDart vertices d n i) := by
  have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) (decodeDart vertices d n i)
  erw [encodeLabeling_decodeLabeling d n labels] at h
  simpa only [encodeDart_decodeDart vertices d n i] using! h

theorem edgeSatisfied_eq_path {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (direction : Bool)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels
      (encodeDart vertices d n (direction, w)) =
    PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
      (finitePortSelector (PortTables.portGraph input) (n + 1)) w
      (decodeLabeling d n labels w.1)
      (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) := by
  rw [edgeSatisfied_decoded input n labels (encodeDart vertices d n (direction, w)),
    decodeDart_encodeDart vertices d n (direction, w)]
  exact PoweringTest.poweredGraph_edgeSatisfied (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels) direction w

theorem rejectionCount_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount
      (encodeLabeling d n labels) = (mathematicalGraph input n).rejectionCount labels := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel
  simpa using!
    GenericGraphTables.enumeratedGraph_rejectionCount (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels

theorem rejectionCount_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount labels =
      (mathematicalGraph input n).rejectionCount (decodeLabeling d n labels) := by
  have h := rejectionCount_encoded input n (decodeLabeling d n labels)
  erw [encodeLabeling_decodeLabeling d n labels] at h
  exact h

theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) e
    erw [encodeLabeling_decodeLabeling d n labels] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

theorem path_rejection_mean_eq_table_fraction {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (labels : EncodedLabeling vertices d n) :
    SpectralReturn.mean (fun w : Walk (Fin vertices) (Fin d) (n + 1) =>
      PoweringMoment.bit
        (PoweringTest.pathAccepts (PortTables.portGraph input) (PortTables.accepts input) n
          (finitePortSelector (PortTables.portGraph input) (n + 1)) w
          (decodeLabeling d n labels w.1)
          (decodeLabeling d n labels (endpoint (PortTables.portGraph input) w)) = false)) =
      ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) /
        ((table input n).darts : ℝ) := by
  rw [rejectionCount_decoded input n labels, ← card_darts_eq_table input n]
  exact PoweringCounting.path_rejection_mean_eq_count (PortTables.portGraph input)
    (PortTables.accepts input) n (finitePortSelector (PortTables.portGraph input) (n + 1))
    (decodeLabeling d n labels)

theorem uniform_count_gap_iff {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ) :
    (∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ)) ↔
    (∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) := by
  constructor
  · intro h labels
    have hlabels := h (encodeLabeling d n labels)
    erw [rejectionCount_encoded input n labels, ← card_darts_eq_table input n] at hlabels
    exact hlabels
  · intro h labels
    rw [rejectionCount_decoded input n labels]
    have hlabels := h (decodeLabeling d n labels)
    rw [card_darts_eq_table input n] at hlabels
    exact hlabels

theorem uniform_count_gap {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ)
    (hgap : ∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) :
    ∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) :=
  (uniform_count_gap_iff input n epsilon).mpr hgap

end BinPackingGames.Foundations.PCP.PoweringTableSemantics

end OAI
