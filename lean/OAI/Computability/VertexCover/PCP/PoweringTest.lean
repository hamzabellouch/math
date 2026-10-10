import Mathlib
import OAI.Computability.VertexCover.PCP.ConstraintGraph
import OAI.Computability.VertexCover.PCP.PoweringOpinions
import OAI.Computability.VertexCover.PCP.PoweringReach

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.PoweringTest

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

end UniqueGames.Foundations.PCP.PoweringTest

end OAI
