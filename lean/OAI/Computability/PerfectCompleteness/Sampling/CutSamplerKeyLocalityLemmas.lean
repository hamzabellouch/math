import OAI.Computability.PerfectCompleteness.Construction.TreeCanonical
import OAI.Computability.PerfectCompleteness.Foundations.CutTerminalZero
import OAI.Computability.PerfectCompleteness.Repetition.CleanCountingLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerLocality

namespace OAI


namespace PerfectCompleteness.CutSamplerKeyLocality

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open CutSamplerLocality

abbrev F2 := ZMod 2

noncomputable section

universe u

variable {branch : Nat → Nat} {n m t : Nat}

def keptLeaf : {n m : Nat} → Path branch n (m + 1) →
    (Fin (branch m) → Prop) → Slots branch n → Prop
  | _, _, .refl _, clean, s => ¬ clean s.1
  | _, _, .step i p, clean, s => s.1 ≠ i ∨ keptLeaf p clean s.2

theorem view_eq_of_keptLeaf (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (x y : Assignment A),
      (∀ s, keptLeaf p clean s → x s = y s) → view p A clean x = view p A clean y := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean x y hagree
          funext i s
          exact hagree (i.val, s) i.property
      | step i p =>
          intro A clean x y hagree
          apply Prod.ext
          · funext j s
            exact hagree (j.val, s) (Or.inl j.property)
          · apply ih p (childFamily A i) clean
              (childRestriction A i x) (childRestriction A i y)
            intro s hs
            exact hagree (i, s) (Or.inr hs)

theorem keptLeaf_at_cut (p : Path branch n (m + 1))
    (clean : Fin (branch m) → Prop) (i : Fin (branch m)) (s : Slots branch m) :
    keptLeaf p clean (p.slotEmbedding (i, s)) ↔ ¬ clean i := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl => rfl
      | step j p =>
          change (j ≠ j ∨ keptLeaf p clean (p.slotEmbedding (i, s))) ↔ ¬ clean i
          simpa only [ne_self_iff_false, false_or] using ih p clean i s

def numberedKeep (p : Path branch n (m + 1)) (clean : Fin (branch m) → Prop) :
    Fin (TreeCanonical.locationCount branch n t) → Prop :=
  fun j => keptLeaf p clean ((TreeCanonical.numbering branch n t).symm j).1

theorem not_numberedKeep_clean (p : Path branch n (m + 1))
    (clean : Fin (branch m) → Prop) (i : Fin (branch m)) (hi : clean i)
    (s : Slots branch m) (k : Fin t) :
    ¬ numberedKeep p clean
      (TreeCanonical.numbering branch n t (p.slotEmbedding (i, s), k)) := by
  intro h
  have hkeep : keptLeaf p clean (p.slotEmbedding (i, s)) := by
    simpa only [numberedKeep, Equiv.symm_apply_apply] using h
  exact (keptLeaf_at_cut p clean i s).mp hkeep hi

theorem view_eq_of_numbered_retained (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (x y : Domain slots)
    (hret : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean)
        (TreeCanonical.assignmentEquiv slots x) =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean)
        (TreeCanonical.assignmentEquiv slots y)) :
    view p (LeafDomain slots) clean x = view p (LeafDomain slots) clean y := by
  apply view_eq_of_keptLeaf p (LeafDomain slots) clean x y
  intro s hs
  funext k
  let j := TreeCanonical.numbering branch n t (s, k)
  have hj : numberedKeep p clean j := by
    simpa only [numberedKeep, j, Equiv.symm_apply_apply] using hs
  have hvalue := congrFun hret ⟨j, hj⟩
  exact Eq.mp (congrArg (fun sk : TreeCanonical.Location branch n t =>
    x sk.1 sk.2 = y sk.1 sk.2)
    ((TreeCanonical.numbering branch n t).symm_apply_apply (s, k))) hvalue

theorem view_eq_of_retained (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (x y : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (hret : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) x =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) y) :
    view p (LeafDomain slots) clean ((TreeCanonical.assignmentEquiv slots).symm x) =
      view p (LeafDomain slots) clean ((TreeCanonical.assignmentEquiv slots).symm y) := by
  apply view_eq_of_numbered_retained p slots clean
  simpa only [Equiv.apply_symm_apply] using hret


variable {J : Type*}
  (repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
  (tapes : J → CutSamplerRefinement.Tape F2 repeats p (LeafDomain slots))

def rowQuery : Domain slots → J → F2 :=
  fun x j => (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain slots) (tapes j)).val x

def numberedRows : MixedSupport.Assignment (TreeCanonical.numberedSlots slots) → J → F2 :=
  TreeCanonical.numberedFunction slots (rowQuery repeats p slots tapes)

def allRowsZero : Prop :=
  ∀ j, ZeroAtClean F2 repeats p (LeafDomain slots) clean (tapes j)

theorem numberedRows_constant (hzero : allRowsZero repeats p slots clean tapes)
    (x y : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (hret : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) x =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) y) :
    numberedRows repeats p slots tapes x = numberedRows repeats p slots tapes y := by
  funext j
  exact evaluate_eq_of_view_eq F2 repeats p (LeafDomain slots) clean (tapes j) (hzero j)
    _ _ (view_eq_of_retained p slots clean x y hret)

def retainedRows : CleanKeyErasure.Retained (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) → J → F2 :=
  numberedRows repeats p slots tapes ∘
    CleanKeyFactorization.fill (TreeCanonical.numberedSlots slots) (numberedKeep p clean)

theorem retainedRows_eq_of_extension (hzero : allRowsZero repeats p slots clean tapes)
    (x : CleanKeyErasure.Retained (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
    (y : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (hy : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) y = x) :
    retainedRows repeats p slots clean tapes x = numberedRows repeats p slots tapes y := by
  apply numberedRows_constant repeats p slots clean tapes hzero
  exact (CleanKeyFactorization.retain_fill (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) x).trans hy.symm

theorem numberedRows_factor (hzero : allRowsZero repeats p slots clean tapes) :
    numberedRows repeats p slots tapes = retainedRows repeats p slots clean tapes ∘
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) := by
  funext x
  exact (retainedRows_eq_of_extension repeats p slots clean tapes hzero _ x rfl).symm

theorem clean_position_dropped (hzero : allRowsZero repeats p slots clean tapes)
    (i : Fin (branch m)) (hi : clean i) (s : Slots branch m) (k : Fin t) :
    MixedSupport.keyFields (TreeCanonical.numberedSlots slots) (numberedRows repeats p slots tapes)
      (TreeCanonical.numbering branch n t (p.slotEmbedding (i, s), k)) = .dropped :=
  CleanKeyErasure.keyFields_dropped_of_retained (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (numberedRows repeats p slots tapes)
    (numberedRows_constant repeats p slots clean tapes hzero) _
    (not_numberedKeep_clean p clean i hi s k)

theorem key_eq_retained (hzero : allRowsZero repeats p slots clean tapes)
    (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots) (numberedRows repeats p slots tapes) =
      CleanKeyFactorization.retainedKey side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedRows repeats p slots clean tapes) := by
  rw [numberedRows_factor repeats p slots clean tapes hzero]
  exact CleanKeyFactorization.key_factor side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedRows repeats p slots clean tapes)

theorem label_eq_retained (hzero : allRowsZero repeats p slots clean tapes)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots slots)
      (numberedRows repeats p slots tapes)).val =
      (labeling (CleanKeyFactorization.retainedQueryKey side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedRows repeats p slots clean tapes))).val := by
  rw [numberedRows_factor repeats p slots clean tapes hzero]
  exact CleanKeyFactorization.label_factor labeling side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedRows repeats p slots clean tapes)

theorem response_eq_retained (hzero : allRowsZero repeats p slots clean tapes)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
      (numberedRows repeats p slots tapes) =
      CleanKeyFactorization.retainedResponse labeling side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedRows repeats p slots clean tapes) := by
  rw [numberedRows_factor repeats p slots clean tapes hzero]
  exact CleanKeyFactorization.response_factor labeling side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedRows repeats p slots clean tapes)


end
end PerfectCompleteness.CutSamplerKeyLocality



namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def Tape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Type (max u w)
  | _, m, .refl _, A, clean =>
      (i : {i : Fin (branch m) // ¬ clean i}) →
        squareSpace (space 𝕜 branch m (childFamily A i.val))
  | n + 1, _, .step i p, A, clean =>
      ((j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val))) ×
        ((call : Fin (repeats (n + 1)) × Bool) → Tape 𝕜 repeats p (childFamily A i) clean)

def erase (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → CutSamplerRefinement.Tape 𝕜 repeats p A →
        Tape 𝕜 repeats p A clean
  | _, _, .refl _, _, _, tape => fun i => tape () i.val
  | _, _, .step i p, A, clean, tape =>
      (fun j => tape (.inl j), fun call => erase 𝕜 repeats p (childFamily A i) clean
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape call.1 call.2))

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Tape 𝕜 repeats p A clean → Assignment A → 𝕜
  | _, m, .refl _, A, clean, tape, x =>
      ∑ i : {i : Fin (branch m) // ¬ clean i}, (tape i).val (childRestriction A i.val x)
  | n + 1, _, .step i p, A, clean, tape, x =>
      (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) +
        ∑ h : Fin (repeats (n + 1)),
          evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)) (childRestriction A i x) *
            evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true)) (childRestriction A i x)

theorem evaluate_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : Tape 𝕜 repeats (.refl (m + 1)) A clean) (x : Assignment A) :
    evaluate 𝕜 repeats (.refl (m + 1)) A clean tape x =
      ∑ i : {i : Fin (branch m) // ¬ clean i}, (tape i).val (childRestriction A i.val x) := rfl

theorem evaluate_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : Tape 𝕜 repeats (.step i p) A clean) (x : Assignment A) :
    evaluate 𝕜 repeats (.step i p) A clean tape x =
      (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) +
        ∑ h : Fin (repeats (n + 1)),
          evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)) (childRestriction A i x) *
            evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true))
              (childRestriction A i x) := rfl

theorem evaluate_erase (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape →
      ∀ x : Assignment A,
        evaluate 𝕜 repeats p A clean (erase 𝕜 repeats p A clean tape) x =
          (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape hzero x
          have heval :
              (UniformChildSum.recursiveSum (𝕜 := 𝕜) A (tape ())).val x =
                ∑ i : Fin (branch n), (tape () i).val (childRestriction A i x) := by
            have hsum := congrFun
              (UniformChildSum.childSum_apply (𝕜 := 𝕜) (childRestriction A)
                (fun i => space 𝕜 branch n (childFamily A i)) (tape ())) x
            simp only [Finset.sum_apply, PointwiseSpaces.pullback_apply] at hsum
            refine hsum.trans ?_
            refine Finset.sum_congr (ι := Fin (branch n)) ?_ ?_
            · ext i
              simp only [Finset.mem_univ]
            · intro i _
              rfl
          rw [evaluate_refl, CutSamplerLocality.evaluate_refl, heval]
          simp only [erase]
          rw [← Fintype.sum_subtype_add_sum_subtype clean
            (fun i => (tape () i).val (childRestriction A i x))]
          have hz : (∑ i : {i : Fin (branch n) // clean i},
              (tape () i.val).val (childRestriction A i.val x)) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [hzero i.val i.property]
            rfl
          rw [hz, zero_add]
      | step i p =>
          intro A clean tape hzero x
          rw [evaluate_step, CutSamplerLocality.evaluate_step]
          simp only [erase, RecursiveSampler.combine, RecursiveSampler.combineFunction,
            Finset.sum_apply, Pi.add_apply, Pi.mul_apply, PointwiseSpaces.pullback_apply]
          apply congrArg (fun z =>
            (∑ j : OffPath i, (tape (.inl j)).val (childRestriction A j.val x)) + z)
          apply Finset.sum_congr rfl
          intro h _
          rw [ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h false) (hzero h false),
            ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h true) (hzero h true)]

theorem evaluate_erase_of_split_zero (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats p A)
    (hzero : ∀ terminal i, clean i →
      (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal i = 0)
    (x : Assignment A) :
    evaluate 𝕜 repeats p A clean (erase 𝕜 repeats p A clean tape) x =
      (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val x :=
  evaluate_erase 𝕜 repeats p A clean tape
    ((CutTerminalZero.zeroAtClean_iff 𝕜 repeats p A clean tape).mp hzero) x

end
end PerfectCompleteness.CutSamplerReplay



namespace PerfectCompleteness.CutSamplerReplayGrouping

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev RetainedTerminal (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (A : Slots branch n → Type u)
    (clean : Fin (branch m) → Prop) :=
  TerminalIndex repeats p → (i : {i : Fin (branch m) // ¬ clean i}) →
    squareSpace (space 𝕜 branch m (childFamily (p.family A) i.val))

def exteriorStepIndex (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (call : Fin (repeats (n + 1)) × Bool)
    (j : CutTerminalSplit.ExteriorIndex repeats p) :
    CutTerminalSplit.ExteriorIndex repeats (.step i p) :=
  ⟨.inr (call, j.val), j.property⟩

def subExterior (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u) (call : Fin (repeats (n + 1)) × Bool)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.step i p) A) :
    CutTerminalSplit.ExteriorTape 𝕜 repeats p (childFamily A i) :=
  fun j => exterior (exteriorStepIndex repeats i p call j)

theorem subExterior_splitTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    subExterior 𝕜 repeats i p A (h, b)
        (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).2 =
      (CutTerminalSplit.splitTape 𝕜 repeats p (childFamily A i)
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).2 := by
  funext j
  rfl

def assemble (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) →
      CutTerminalSplit.ExteriorTape 𝕜 repeats p A →
      RetainedTerminal 𝕜 repeats p A clean → CutSamplerReplay.Tape 𝕜 repeats p A clean
  | _, _, .refl _, _, _, _, terminal => terminal ()
  | _, _, .step i p, A, clean, exterior, terminal =>
      (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩,
        fun call => assemble 𝕜 repeats p (childFamily A i) clean
          (subExterior 𝕜 repeats i p A call exterior)
          (fun location child => terminal (call, location) child))

theorem assemble_splitTape (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      assemble 𝕜 repeats p A clean (CutTerminalSplit.splitTape 𝕜 repeats p A tape).2
          (fun terminal child =>
            (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal child.val) =
        CutSamplerReplay.erase 𝕜 repeats p A clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape
          rfl
      | step i p =>
          intro A clean tape
          apply Prod.ext
          · funext j
            rfl
          · funext call
            rcases call with ⟨h, b⟩
            change assemble 𝕜 repeats p (childFamily A i) clean
                (subExterior 𝕜 repeats i p A (h, b)
                  (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).2)
                (fun terminal child =>
                  (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).1
                    ((h, b), terminal) child.val) =
              CutSamplerReplay.erase 𝕜 repeats p (childFamily A i) clean
                (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)
            rw [subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)

theorem evaluate_assemble_splitTape (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats p A)
    (hzero : CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape) (x : Assignment A) :
    CutSamplerReplay.evaluate 𝕜 repeats p A clean
        (assemble 𝕜 repeats p A clean (CutTerminalSplit.splitTape 𝕜 repeats p A tape).2
          (fun terminal child =>
            (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal child.val)) x =
      (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val x := by
  rw [assemble_splitTape]
  exact CutSamplerReplay.evaluate_erase 𝕜 repeats p A clean tape hzero x

end
end PerfectCompleteness.CutSamplerReplayGrouping

end OAI
