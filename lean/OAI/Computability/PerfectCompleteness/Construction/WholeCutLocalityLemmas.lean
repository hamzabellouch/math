import OAI.Computability.PerfectCompleteness.Foundations.WholeCutExteriorTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerKeyLocalityLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeCutLocality

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluate_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inl ()) =
      BucketSampler.evaluate (rows (n + 1))
        (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots)) tape.1 := rfl

theorem evaluate_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) (node : Nodes branch n) :
    WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inr (i, node)) =
      WholeCutSampler.evaluate rows repeats p (childSlots slots i) tape.2.1 node := by
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_selected]
  rfl

theorem evaluate_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inr (j.val, node)) =
      tape.2.2 j node := by
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_ordinary]
  rfl

theorem joint_eq_of_view_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (tape : WholeCutSampler.Tape rows repeats p slots),
      WholeCutZero.ZeroAtClean rows repeats p slots clean tape →
      ∀ x y : Domain slots,
      CutSamplerLocality.view p (LeafDomain slots) clean x =
        CutSamplerLocality.view p (LeafDomain slots) clean y →
      joint (WholeCutSampler.evaluate rows repeats p slots tape) x =
        joint (WholeCutSampler.evaluate rows repeats p slots tape) y := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape hzero x y hview
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            let scalarTape : CutSamplerRefinement.Tape F2 repeats (.refl (n + 1))
                (LeafDomain slots) := fun _ i => (tape i).1 row
            have hz : CutSamplerLocality.ZeroAtClean F2 repeats (.refl (n + 1))
                (LeafDomain slots) clean scalarTape :=
              fun i hi => (hzero i hi).1 row
            exact CutSamplerLocality.evaluate_eq_of_view_eq F2 repeats (.refl (n + 1))
              (LeafDomain slots) clean scalarTape hz x y hview
          · change ((tape i).2 node row).val
                (restrictNode (childSlots slots i) node (restrictChild slots i x)) =
              ((tape i).2 node row).val
                (restrictNode (childSlots slots i) node (restrictChild slots i y))
            by_cases hi : clean i
            · rw [(hzero i hi).2 node row]
              rfl
            · exact congrArg
                (fun z => ((tape i).2 node row).val (restrictNode (childSlots slots i) node z))
                (congrFun hview ⟨i, hi⟩)
      | step i p =>
          intro slots clean tape hzero x y hview
          have hout : ∀ j : RecursiveSampler.OffPath i,
              restrictChild slots j.val x = restrictChild slots j.val y :=
            congrFun (congrArg Prod.fst hview)
          have hin :
              CutSamplerLocality.view p (LeafDomain (childSlots slots i)) clean
                  (restrictChild slots i x) =
                CutSamplerLocality.view p (LeafDomain (childSlots slots i)) clean
                  (restrictChild slots i y) := congrArg Prod.snd hview
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            change
              (WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inl ()) row).val x =
              (WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inl ()) row).val y
            simp only [evaluate_root]
            have hx := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
              tape.1 row x
            have hy := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
              tape.1 row y
            refine hx.trans (Eq.trans ?_ hy.symm)
            refine Finset.sum_congr (ι := BucketSampler.Direction (rows (n + 1))) ?_ ?_
            · ext v
              simp only [Finset.mem_univ]
            · intro v _
              exact congrArg (fun z : F2 => v.val row * z)
                (CutSamplerLocality.evaluate_eq_of_view_eq F2 repeats (.step i p)
                  (LeafDomain slots) clean (tape.1 v) (hzero.1 v) x y hview)
          · by_cases hji : j = i
            · subst j
              have hselected := ih p (childSlots slots i) clean tape.2.1 hzero.2
                (restrictChild slots i x) (restrictChild slots i y) hin
              have hrow := congrFun (congrFun hselected node) row
              change
                (WholeCutSampler.evaluate rows repeats (.step i p) slots tape
                  (.inr (i, node)) row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i x)) =
                (WholeCutSampler.evaluate rows repeats (.step i p) slots tape
                  (.inr (i, node)) row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i y))
              simp only [evaluate_selected]
              exact hrow
            · change
                (WholeCutSampler.evaluate rows repeats (.step i p) slots tape
                  (.inr (j, node)) row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j x)) =
                (WholeCutSampler.evaluate rows repeats (.step i p) slots tape
                  (.inr (j, node)) row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j y))
              rw [evaluate_ordinary rows repeats i p slots tape ⟨j, hji⟩ node]
              rw [hout ⟨j, hji⟩]

theorem joint_eq_of_grouped_zero (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (x y : Domain slots)
    (hview : CutSamplerLocality.view p (LeafDomain slots) clean x =
      CutSamplerLocality.view p (LeafDomain slots) clean y) :
    joint (WholeCutSampler.evaluate rows repeats p slots tape) x =
      joint (WholeCutSampler.evaluate rows repeats p slots tape) y :=
  joint_eq_of_view_eq rows repeats p slots clean tape
    ((WholeCutZero.grouped_iff rows repeats p slots clean tape).mp hzero) x y hview

theorem fullJoint_eq_of_grouped_zero (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (x y : Domain slots)
    (hview : CutSamplerLocality.view p (LeafDomain slots) clean x =
      CutSamplerLocality.view p (LeafDomain slots) clean y) :
    fullJoint (WholeCutSampler.evaluate rows repeats p slots tape) x =
      fullJoint (WholeCutSampler.evaluate rows repeats p slots tape) y :=
  Prod.ext (joint_eq_of_grouped_zero rows repeats p slots clean tape hzero x y hview) rfl

end
end PerfectCompleteness.WholeCutLocality

end

section

namespace PerfectCompleteness.WholeCutKeyLocality

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat} {Y : Type*}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (clean : Fin (branch m) → Prop)
  (tape : WholeCutSampler.Tape rows repeats p slots)
  (post : Output branch n rows → Y)

def query : MixedSupport.Assignment (TreeCanonical.numberedSlots slots) → Y :=
  post ∘ TreeCanonical.numberedFunction slots
    (fullJoint (WholeCutSampler.evaluate rows repeats p slots tape))

theorem query_constant
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (x y : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (hret : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) x =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) y) :
    query rows repeats p slots tape post x = query rows repeats p slots tape post y :=
  congrArg post (WholeCutLocality.fullJoint_eq_of_grouped_zero rows repeats p slots clean
    tape hzero _ _ (view_eq_of_retained p slots clean x y hret))

def retainedQuery : CleanKeyErasure.Retained (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) → Y :=
  query rows repeats p slots tape post ∘
    CleanKeyFactorization.fill (TreeCanonical.numberedSlots slots) (numberedKeep p clean)

theorem retainedQuery_eq_of_extension
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (x : CleanKeyErasure.Retained (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
    (y : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (hy : CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) y = x) :
    retainedQuery rows repeats p slots clean tape post x =
      query rows repeats p slots tape post y := by
  apply query_constant rows repeats p slots clean tape post hzero
  exact (CleanKeyFactorization.retain_fill (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) x).trans hy.symm

theorem query_factor
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) :
    query rows repeats p slots tape post = retainedQuery rows repeats p slots clean tape post ∘
      CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) := by
  funext x
  exact (retainedQuery_eq_of_extension rows repeats p slots clean tape post hzero _ x rfl).symm

theorem clean_position_dropped
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (i : Fin (branch m)) (hi : clean i) (s : Slots branch m) (k : Fin t) :
    MixedSupport.keyFields (TreeCanonical.numberedSlots slots)
      (query rows repeats p slots tape post)
      (TreeCanonical.numbering branch n t (p.slotEmbedding (i, s), k)) = .dropped :=
  CleanKeyErasure.keyFields_dropped_of_retained (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (query rows repeats p slots tape post)
    (query_constant rows repeats p slots clean tape post hzero) _
    (not_numberedKeep_clean p clean i hi s k)

theorem key_eq_retained
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots)
      (query rows repeats p slots tape post) =
      CleanKeyFactorization.retainedKey side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedQuery rows repeats p slots clean tape post) := by
  rw [query_factor rows repeats p slots clean tape post hzero]
  exact CleanKeyFactorization.key_factor side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedQuery rows repeats p slots clean tape post)

theorem label_eq_retained
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots slots)
      (query rows repeats p slots tape post)).val =
      (labeling (CleanKeyFactorization.retainedQueryKey side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedQuery rows repeats p slots clean tape post))).val := by
  rw [query_factor rows repeats p slots clean tape post hzero]
  exact CleanKeyFactorization.label_factor labeling side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedQuery rows repeats p slots clean tape post)

theorem response_eq_retained
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
      (query rows repeats p slots tape post) =
      CleanKeyFactorization.retainedResponse labeling side (numberedKeep p clean)
        (CleanKeyFactorization.retainedSlots (TreeCanonical.numberedSlots slots) (numberedKeep p clean))
        (retainedQuery rows repeats p slots clean tape post) := by
  rw [query_factor rows repeats p slots clean tape post hzero]
  exact CleanKeyFactorization.response_factor labeling side (TreeCanonical.numberedSlots slots)
    (numberedKeep p clean) (retainedQuery rows repeats p slots clean tape post)

end
end PerfectCompleteness.WholeCutKeyLocality

end

end OAI
