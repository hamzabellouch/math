import OAI.Computability.PerfectCompleteness.Construction.RelativeDescendantProductsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.StoppedSharedEvents
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedOwnInputGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

theorem exists_relativePath {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    ∃ p : Path branch (Nodes.height upper) (Nodes.height lower),
      (Nodes.path upper).append p = Nodes.path lower := by
  induction h with
  | root i lower => exact ⟨.step i (Nodes.path lower), rfl⟩
  | child i h ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨p, congrArg (Path.step i) hp⟩

def cutOfBelow {upper lower : Nodes branch n} (h : Below branch upper lower) :
    OwnInputReference.Cut upper lower where
  proper := h.height_lt
  path := Classical.choose (exists_relativePath h)
  slots_agree := by
    intro s
    rw [← Path.slotEmbedding_append, Classical.choose_spec (exists_relativePath h)]

theorem fullPath_cutOfBelow {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    WholeArrayInteriorOwnInputLaw.fullPath upper lower (cutOfBelow h) =
      Nodes.path lower :=
  Classical.choose_spec (exists_relativePath h)

theorem nodeAtLevel_endpoint : {n k : Nat} → (p : Path branch n (k + 1)) →
    (suffix : Slots branch (k + 1)) →
    GeometricPath.nodeAtLevel (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ =
      WholeArrayInteriorExterior.upperNode p
  | _, _, .refl _, suffix => GeometricPath.nodeAtLevel_last suffix
  | N + 1, k, .step i p, suffix => by
      change GeometricPath.nodeAtLevel (branch := branch) (n := N + 1) (i, p.slotEmbedding suffix)
          (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin N).castSucc =
        Sum.inr (i, WholeArrayInteriorExterior.upperNode p)
      exact (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := N)
        (i, p.slotEmbedding suffix)
        (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin N)).trans
          (congrArg (fun node : Nodes branch N =>
            (Sum.inr (i, node) : Nodes branch (N + 1))) (nodeAtLevel_endpoint p suffix))

theorem nodeAtLevel_endpoint_spec {k : Nat} (p : Path branch n (k + 1))
    (suffix : Slots branch (k + 1)) :
    (⟨Nodes.height (GeometricPath.nodeAtLevel (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩),
      Nodes.path (GeometricPath.nodeAtLevel (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩)⟩ :
      Σ height, Path branch n height) = ⟨k + 1, p⟩ := by
  rw [nodeAtLevel_endpoint]
  exact WholeArrayInteriorExterior.upperNode_spec p

def pathTapeEquiv {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q) :
    WholeArraySampler.Tape rows repeats p.2 slots ≃
      WholeArraySampler.Tape rows repeats q.2 slots :=
  Equiv.cast (congrArg
    (fun path : Σ height, Path branch n height =>
      WholeArraySampler.Tape rows repeats path.2 slots) h)

theorem pathTapeEquiv_law {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q) :
    (WholeArraySampler.tapeLaw rows repeats p.2 slots).pushforward
        (pathTapeEquiv rows repeats slots h) =
      WholeArraySampler.tapeLaw rows repeats q.2 slots := by
  cases h
  exact FiniteDistribution.pushforward_id _

theorem evaluate_pathTapeEquiv {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q)
    (ω : WholeArraySampler.Tape rows repeats p.2 slots) :
    WholeArraySampler.evaluate rows repeats q.2 slots
        (pathTapeEquiv rows repeats slots h ω) =
      WholeArraySampler.evaluate rows repeats p.2 slots ω := by
  cases h
  rfl

variable {m t cut : Nat} {rows : Nat → Nat}

def lowerLevel (hcut : cut + 1 ≤ n) : Fin n :=
  ⟨cut, Nat.lt_of_lt_of_le (Nat.lt_succ_self cut) hcut⟩

def upperNode (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows) (level : Fin n) :
    Nodes branch n :=
  GeometricPath.nodeAtLevel (StoppedSharedEvents.representativeLeaf hcut hbranch context) level

def lowerNode (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows) : Nodes branch n :=
  GeometricPath.nodeAtLevel (StoppedSharedEvents.representativeLeaf hcut hbranch context)
    (lowerLevel hcut)

@[simp] theorem upperNode_height (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows) (level : Fin n) :
    Nodes.height (upperNode hcut hbranch context level) = level.val + 1 :=
  GeometricPath.nodeAtLevel_height _ _

@[simp] theorem lowerNode_height (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows) :
    Nodes.height (lowerNode hcut hbranch context) = cut + 1 :=
  GeometricPath.nodeAtLevel_height _ _

def ownCut (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val) :
    OwnInputReference.Cut (upperNode hcut hbranch context level)
      (lowerNode hcut hbranch context) :=
  cutOfBelow (GeometricDescendants.below_nodeAtLevel
    (StoppedSharedEvents.representativeLeaf hcut hbranch context) level
    (lowerLevel hcut) hlevel)

theorem lowerNode_path_spec (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows) :
    (⟨Nodes.height (lowerNode hcut hbranch context),
      Nodes.path (lowerNode hcut hbranch context)⟩ : Σ height, Path branch n height) =
      ⟨cut + 1, GeometricCutSplit.prefixPath hcut context.2.1⟩ :=
  nodeAtLevel_endpoint_spec (GeometricCutSplit.prefixPath hcut context.2.1)
    (StoppedSharedEvents.referenceSuffix hcut hbranch)

theorem fullPath_spec (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val) :
    (⟨Nodes.height (lowerNode hcut hbranch context),
      WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
        (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel)⟩ :
      Σ height, Path branch n height) =
      ⟨cut + 1, GeometricCutSplit.prefixPath hcut context.2.1⟩ := by
  have hpath :
      WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
        (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel) =
      Nodes.path (lowerNode hcut hbranch context) :=
    fullPath_cutOfBelow (GeometricDescendants.below_nodeAtLevel
      (StoppedSharedEvents.representativeLeaf hcut hbranch context) level
      (lowerLevel hcut) hlevel)
  exact (congrArg (fun p : Path branch n (Nodes.height (lowerNode hcut hbranch context)) =>
    (⟨Nodes.height (lowerNode hcut hbranch context), p⟩ : Σ height, Path branch n height))
      hpath).trans (lowerNode_path_spec hcut hbranch context)

theorem arrayLaw_eq (repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val) :
    WholeArraySampler.law rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
          (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel)) slots =
      WholeArraySampler.law rows repeats (GeometricCutSplit.prefixPath hcut context.2.1) slots :=
  congrArg (fun path : Σ height, Path branch n height =>
    WholeArraySampler.law rows repeats path.2 slots)
      (fullPath_spec hcut hbranch context level hlevel)

def tapeEquiv (repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val) :
    WholeArraySampler.Tape rows repeats (GeometricCutSplit.prefixPath hcut context.2.1) slots ≃
      WholeArraySampler.Tape rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
          (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel)) slots :=
  pathTapeEquiv rows repeats slots (fullPath_spec hcut hbranch context level hlevel).symm

theorem tapeEquiv_law (repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val) :
    (WholeArraySampler.tapeLaw rows repeats
      (GeometricCutSplit.prefixPath hcut context.2.1) slots).pushforward
        (tapeEquiv repeats slots hcut hbranch context level hlevel) =
      WholeArraySampler.tapeLaw rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
          (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel)) slots :=
  pathTapeEquiv_law rows repeats slots (fullPath_spec hcut hbranch context level hlevel).symm

theorem evaluate_tapeEquiv (repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val)
    (ω : WholeArraySampler.Tape rows repeats
      (GeometricCutSplit.prefixPath hcut context.2.1) slots) :
    WholeArraySampler.evaluate rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (upperNode hcut hbranch context level)
          (lowerNode hcut hbranch context) (ownCut hcut hbranch context level hlevel)) slots
        (tapeEquiv repeats slots hcut hbranch context level hlevel ω) =
      WholeArraySampler.evaluate rows repeats (GeometricCutSplit.prefixPath hcut context.2.1)
        slots ω :=
  evaluate_pathTapeEquiv rows repeats slots
    (fullPath_spec hcut hbranch context level hlevel).symm ω

theorem exposedRead_law (repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : StoppedSharedSampler.Context branch n t m cut rows)
    (level : Fin n) (hlevel : cut < level.val)
    (W : Submodule (ZMod 2) (Block rows (upperNode hcut hbranch context level))) :
    (WholeArraySampler.tapeLaw rows repeats
      (GeometricCutSplit.prefixPath hcut context.2.1) slots).pushforward
        (fun ω => WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots
          (upperNode hcut hbranch context level) (lowerNode hcut hbranch context)
          (ownCut hcut hbranch context level hlevel) W
          (tapeEquiv repeats slots hcut hbranch context level hlevel ω)) =
      OwnInputReference.rawLaw slots rows (upperNode hcut hbranch context level)
        (lowerNode hcut hbranch context) W repeats (ownCut hcut hbranch context level hlevel)
        (WholeArrayInteriorOwnInputLaw.exteriorLaw rows repeats slots
          (upperNode hcut hbranch context level) (lowerNode hcut hbranch context)
          (ownCut hcut hbranch context level hlevel)) := by
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (GeometricCutSplit.prefixPath hcut context.2.1) slots)
    (tapeEquiv repeats slots hcut hbranch context level hlevel)
    (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots
      (upperNode hcut hbranch context level) (lowerNode hcut hbranch context)
      (ownCut hcut hbranch context level hlevel) W)]
  rw [tapeEquiv_law]
  exact WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots
    (upperNode hcut hbranch context level) (lowerNode hcut hbranch context)
    (ownCut hcut hbranch context level hlevel) W

end
end PerfectCompleteness.StoppedOwnInputGeometry

end

end OAI
