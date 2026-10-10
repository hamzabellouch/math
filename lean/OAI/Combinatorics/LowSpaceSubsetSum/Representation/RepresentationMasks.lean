import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSurvival

namespace OAI

/-!
# Actual solution subsets behind the surviving representation

An arbitrary deterministic background assignment is allowed: its precise
integer allocation affects resource costs, but not the survival identities.
Filtering the outside indices by that assignment makes the pieces disjoint
without imposing another probabilistic assumption.
-/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

open scoped symmDiff
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (R : RepresentationSetup n)

def mixerUnion (z : Layout n) : Finset (Fin n) :=
  (R.orderedMixers z 0 ∪ R.orderedMixers z 1) ∪ R.orderedMixers z 2

def outside (z : Layout n) : Finset (Fin n) := z.2 \ R.mixerUnion z

/-- The program's prescribed background allocation gives one such function. -/
abbrev BackgroundAssignment (n : ℕ) := Layout n → Guesses n → Fin n → Fin 4

def background (B : BackgroundAssignment n) (z : Layout n) (g : Guesses n)
    (c : Fin 4) : Finset (Fin n) :=
  (R.outside z).filter (fun i => B z g i = c)

def leftBackground (B : BackgroundAssignment n) (z : Layout n) (g : Guesses n) :
    Finset (Fin n) := R.background B z g 0 ∪ R.background B z g 1

theorem orderedMixers_disjoint (z : Layout n) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (R.orderedMixers z i) (R.orderedMixers z j) := by
  have h := R.disjoint (R.mixerOrder z i) (R.mixerOrder z j)
    (fun he => hij ((R.mixerOrder z).injective he))
  exact (Finset.disjoint_map z.1.toEmbedding).mpr h

theorem background_subset_outside (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) (c : Fin 4) : R.background B z g c ⊆ R.outside z :=
  Finset.filter_subset _ _

theorem background_disjoint_mixer (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) (c : Fin 4) (i : Fin 3) :
    Disjoint (R.background B z g c) (R.orderedMixers z i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hm
  have ho := (Finset.mem_sdiff.mp (R.background_subset_outside B z g c hx)).2
  apply ho
  fin_cases i
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
  · exact Finset.mem_union_right _ hm

theorem background_disjoint (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) {c d : Fin 4} (hcd : c ≠ d) :
    Disjoint (R.background B z g c) (R.background B z g d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hcd ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

theorem leftBackground_disjoint_mixer (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) (i : Fin 3) :
    Disjoint (R.leftBackground B z g) (R.orderedMixers z i) :=
  Finset.disjoint_union_left.mpr
    ⟨R.background_disjoint_mixer B z g 0 i, R.background_disjoint_mixer B z g 1 i⟩

theorem background_subset_solution (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) (c : Fin 4) : R.background B z g c ⊆ z.2 :=
  (R.background_subset_outside B z g c).trans Finset.sdiff_subset

theorem leftBackground_subset_solution (B : BackgroundAssignment n) (z : Layout n)
    (g : Guesses n) : R.leftBackground B z g ⊆ z.2 :=
  Finset.union_subset (R.background_subset_solution B z g 0)
    (R.background_subset_solution B z g 1)

/-- Child one uses top blocks one and two. Child two uses the remaining
top blocks, each once, exactly as in the manuscript's leaf layout. -/
def firstTop (z : Layout n) (f : R.Partitions z) (D : Finset (Fin n)) : Finset (Fin n) :=
  D.filter (fun x => ∃ hx : x ∈ R.orderedMixers z 0, ((f 0).val ⟨x, hx⟩).val < 2)

theorem firstTop_subset (z : Layout n) (f : R.Partitions z) (D : Finset (Fin n)) :
    R.firstTop z f D ⊆ D := Finset.filter_subset _ _

def actualOffsets (B : BackgroundAssignment n) : R.ResidueOffsets where
  parent h := weight (R.signedWeights h.1.1) (R.leftBackground B h.1.1 h.1.2) +
    weight (R.signedWeights h.1.1) (R.selectedHalves h.1.1 1)
  left h x := weight (R.signedWeights h.1.1) (R.background B h.1.1 h.1.2 0) +
    weight (R.signedWeights h.1.1)
      (R.firstTop h.1.1 h.2 (R.retainedMask h.1.1 h.1.2 h.2 0 x))
  right h x := weight (R.signedWeights h.1.1) (R.background B h.1.1 h.1.2 2) +
    weight (R.signedWeights h.1.1)
      (R.firstTop h.1.1 h.2 (R.selectedHalves h.1.1 0 \ R.retainedMask h.1.1 h.1.2 h.2 0 x))

def leftParent (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) :=
  (R.chosenMasks (R.actualOffsets B) h r 0 ∪ R.selectedHalves h.1.1.1 1) ∪
    R.leftBackground B h.1.1.1 h.1.1.2

def rightParent (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) := h.1.1.1.2 \ R.leftParent B h r

def firstLeftChild (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) :=
  (R.chosenMasks (R.actualOffsets B) h r 1 ∪
    R.firstTop h.1.1.1 h.1.2 (R.chosenMasks (R.actualOffsets B) h r 0)) ∪
      R.background B h.1.1.1 h.1.1.2 0

def secondLeftChild (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) := R.leftParent B h r \ R.firstLeftChild B h r

def firstRightChild (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) :=
  (R.chosenMasks (R.actualOffsets B) h r 2 ∪
    R.firstTop h.1.1.1 h.1.2
      (R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0)) ∪
      R.background B h.1.1.1 h.1.1.2 2

def secondRightChild (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Finset (Fin n) := R.rightParent B h r \ R.firstRightChild B h r

theorem leftParent_subset_solution (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    R.leftParent B h r ⊆ h.1.1.1.2 := by
  have hm := (R.chosenMasks_spec (R.actualOffsets B) hr 0).1
  exact Finset.union_subset
    (Finset.union_subset (hm.trans Finset.inter_subset_left) Finset.inter_subset_left)
    (R.leftBackground_subset_solution B _ _)

theorem firstLeftChild_subset_parent (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    R.firstLeftChild B h r ⊆ R.leftParent B h r := by
  have hm := (R.chosenMasks_spec (R.actualOffsets B) hr 1).1
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hm hx))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (R.firstTop_subset _ _ _ hx))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)

theorem selectedHalves_disjoint (z : Layout n) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (R.selectedHalves z i) (R.selectedHalves z j) :=
  (R.orderedMixers_disjoint z hij).mono Finset.inter_subset_right Finset.inter_subset_right

private theorem disjoint_three_unions {ι : Type*} [DecidableEq ι]
    {A B C D E F : Finset ι}
    (had : Disjoint A D) (hae : Disjoint A E) (haf : Disjoint A F)
    (hbd : Disjoint B D) (hbe : Disjoint B E) (hbf : Disjoint B F)
    (hcd : Disjoint C D) (hce : Disjoint C E) (hcf : Disjoint C F) :
    Disjoint ((A ∪ B) ∪ C) ((D ∪ E) ∪ F) := by
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_union_left.mpr
    exact ⟨Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨had, hae⟩, haf⟩,
      Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨hbd, hbe⟩, hbf⟩⟩
  · exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨hcd, hce⟩, hcf⟩

theorem firstRightChild_disjoint_left (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    Disjoint (R.firstRightChild B h r) (R.leftParent B h r) := by
  have h0 := (R.chosenMasks_spec (R.actualOffsets B) hr 0).1
  have h2 := (R.chosenMasks_spec (R.actualOffsets B) hr 2).1
  have ht := R.firstTop_subset h.1.1.1 h.1.2
    (R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0)
  have ht0 := ht.trans Finset.sdiff_subset
  have hb (c : Fin 4) (i : Fin 3) := R.background_disjoint_mixer B h.1.1.1 h.1.1.2 c i
  have hbL (i : Fin 3) := R.leftBackground_disjoint_mixer B h.1.1.1 h.1.1.2 i
  apply disjoint_three_unions
  · exact (R.selectedHalves_disjoint _ (by decide : (2 : Fin 3) ≠ 0)).mono h2 h0
  · exact (R.selectedHalves_disjoint _ (by decide : (2 : Fin 3) ≠ 1)).mono_left h2
  · exact (hbL 2).symm.mono_left (h2.trans (R.selectedHalves_subset _ _))
  · exact Finset.sdiff_disjoint.mono_left ht
  · exact (R.selectedHalves_disjoint _ (by decide : (0 : Fin 3) ≠ 1)).mono_left ht0
  · exact (hbL 0).symm.mono_left (ht0.trans (R.selectedHalves_subset _ _))
  · exact (hb 2 0).mono_right (h0.trans (R.selectedHalves_subset _ _))
  · exact (hb 2 1).mono_right (R.selectedHalves_subset _ _)
  · exact Finset.disjoint_union_right.mpr
      ⟨R.background_disjoint B _ _ (by decide : (2 : Fin 4) ≠ 0),
        R.background_disjoint B _ _ (by decide : (2 : Fin 4) ≠ 1)⟩

theorem firstRightChild_subset_parent (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    R.firstRightChild B h r ⊆ R.rightParent B h r := by
  have h2 := (R.chosenMasks_spec (R.actualOffsets B) hr 2).1
  have ht := R.firstTop_subset h.1.1.1 h.1.2
    (R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0)
  have hs : R.firstRightChild B h r ⊆ h.1.1.1.2 :=
    Finset.union_subset (Finset.union_subset (h2.trans Finset.inter_subset_left)
      ((ht.trans Finset.sdiff_subset).trans Finset.inter_subset_left))
      (R.background_subset_solution B _ _ 2)
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨hs hx,
    fun hl => Finset.disjoint_left.mp (R.firstRightChild_disjoint_left B hr) hx hl⟩

theorem leftParent_weight (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    weight (R.signedWeights h.1.1.1) (R.leftParent B h r) =
      R.chosenWeights (R.actualOffsets B) h r 0 + (R.actualOffsets B).parent h.1 := by
  have h0 := (R.chosenMasks_spec (R.actualOffsets B) hr 0).1
  have hw := (R.chosenMasks_spec (R.actualOffsets B) hr 0).2.2.1
  have hd : Disjoint (R.chosenMasks (R.actualOffsets B) h r 0)
      (R.selectedHalves h.1.1.1 1) :=
    (R.selectedHalves_disjoint _ (by decide : (0 : Fin 3) ≠ 1)).mono_left h0
  have hb : Disjoint
      (R.chosenMasks (R.actualOffsets B) h r 0 ∪ R.selectedHalves h.1.1.1 1)
      (R.leftBackground B h.1.1.1 h.1.1.2) :=
    Finset.disjoint_union_left.mpr
      ⟨(R.leftBackground_disjoint_mixer B _ _ 0).symm.mono_left
          (h0.trans (R.selectedHalves_subset _ _)),
        (R.leftBackground_disjoint_mixer B _ _ 1).symm.mono_left
          (R.selectedHalves_subset _ _)⟩
  rw [leftParent, weight_union _ hb, weight_union _ hd, hw]
  dsimp only [actualOffsets]
  ring

theorem rightParent_weight (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    weight (R.signedWeights h.1.1.1) (R.rightParent B h r) =
      R.signedTarget h.1.1.1 -
        (R.chosenWeights (R.actualOffsets B) h r 0 + (R.actualOffsets B).parent h.1) := by
  rw [rightParent, weight_complement _ (R.leftParent_subset_solution B hr),
    R.signed_solution, R.leftParent_weight B hr]

theorem firstLeftChild_weight (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    weight (R.signedWeights h.1.1.1) (R.firstLeftChild B h r) =
      R.chosenWeights (R.actualOffsets B) h r 1 +
        (R.actualOffsets B).left h.1 (R.chosenWeights (R.actualOffsets B) h r 0) := by
  have h0 := (R.chosenMasks_spec (R.actualOffsets B) hr 0).1
  have h1 := (R.chosenMasks_spec (R.actualOffsets B) hr 1).1
  have hw := (R.chosenMasks_spec (R.actualOffsets B) hr 1).2.2.1
  have ht := (R.firstTop_subset h.1.1.1 h.1.2
    (R.chosenMasks (R.actualOffsets B) h r 0)).trans h0
  have hd := (R.selectedHalves_disjoint h.1.1.1 (by decide : (1 : Fin 3) ≠ 0)).mono h1 ht
  have hb : Disjoint
      (R.chosenMasks (R.actualOffsets B) h r 1 ∪
        R.firstTop h.1.1.1 h.1.2 (R.chosenMasks (R.actualOffsets B) h r 0))
      (R.background B h.1.1.1 h.1.1.2 0) :=
    Finset.disjoint_union_left.mpr
      ⟨(R.background_disjoint_mixer B _ _ 0 1).symm.mono_left
          (h1.trans (R.selectedHalves_subset _ _)),
        (R.background_disjoint_mixer B _ _ 0 0).symm.mono_left
          (ht.trans (R.selectedHalves_subset _ _))⟩
  rw [firstLeftChild, weight_union _ hb, weight_union _ hd, hw]
  change _ = _ + (weight _ _ + weight _ (R.firstTop _ _ (R.chosenMasks _ _ _ 0)))
  ring

theorem firstRightChild_weight (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    weight (R.signedWeights h.1.1.1) (R.firstRightChild B h r) =
      R.chosenWeights (R.actualOffsets B) h r 2 +
        (R.actualOffsets B).right h.1 (R.chosenWeights (R.actualOffsets B) h r 0) := by
  have h2 := (R.chosenMasks_spec (R.actualOffsets B) hr 2).1
  have hw := (R.chosenMasks_spec (R.actualOffsets B) hr 2).2.2.1
  have ht := (R.firstTop_subset h.1.1.1 h.1.2
    (R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0)).trans
      Finset.sdiff_subset
  have hd := (R.selectedHalves_disjoint h.1.1.1 (by decide : (2 : Fin 3) ≠ 0)).mono h2 ht
  have hb : Disjoint
      (R.chosenMasks (R.actualOffsets B) h r 2 ∪
        R.firstTop h.1.1.1 h.1.2
          (R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0))
      (R.background B h.1.1.1 h.1.1.2 2) :=
    Finset.disjoint_union_left.mpr
      ⟨(R.background_disjoint_mixer B _ _ 2 2).symm.mono_left
          (h2.trans (R.selectedHalves_subset _ _)),
        (R.background_disjoint_mixer B _ _ 2 0).symm.mono_left
          (ht.trans (R.selectedHalves_subset _ _))⟩
  rw [firstRightChild, weight_union _ hb, weight_union _ hd, hw]
  change _ = _ + (weight _ _ + weight _
    (R.firstTop _ _ (_ \ R.chosenMasks _ _ _ 0)))
  ring

theorem parents_partition (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    Disjoint (R.leftParent B h r) (R.rightParent B h r) ∧
      R.leftParent B h r ∪ R.rightParent B h r = h.1.1.1.2 :=
  ⟨Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (R.leftParent_subset_solution B hr)⟩

theorem children_partition (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    (Disjoint (R.firstLeftChild B h r) (R.secondLeftChild B h r) ∧
      R.firstLeftChild B h r ∪ R.secondLeftChild B h r = R.leftParent B h r) ∧
    (Disjoint (R.firstRightChild B h r) (R.secondRightChild B h r) ∧
      R.firstRightChild B h r ∪ R.secondRightChild B h r = R.rightParent B h r) :=
  ⟨⟨Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (R.firstLeftChild_subset_parent B hr)⟩,
    ⟨Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (R.firstRightChild_subset_parent B hr)⟩⟩

def ActualFilters (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) : Prop :=
  let w := weight (R.signedWeights h.1.1.1)
  let p := prefixModulus h.2.val
  w (R.leftParent B h r) ≡ (r.1.val : ℤ) [ZMOD (p 0 : ℤ)] ∧
  w (R.rightParent B h r) ≡ R.signedTarget h.1.1.1 - (r.1.val : ℤ) [ZMOD (p 0 : ℤ)] ∧
  w (R.firstLeftChild B h r) ≡ (r.2.1.val : ℤ) [ZMOD (p 1 : ℤ)] ∧
  w (R.secondLeftChild B h r) ≡ (r.1.val : ℤ) - r.2.1.val [ZMOD (p 1 : ℤ)] ∧
  w (R.firstRightChild B h r) ≡ (r.2.2.val : ℤ) [ZMOD (p 2 : ℤ)] ∧
  w (R.secondRightChild B h r) ≡
    (R.signedTarget h.1.1.1 - (r.1.val : ℤ)) - r.2.2.val [ZMOD (p 2 : ℤ)]

theorem actualFilters_of_hits (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    R.ActualFilters B h r := by
  have hc := R.chosenWeights_compatible (R.actualOffsets B) hr
  have hl2 : weight (R.signedWeights h.1.1.1) (R.secondLeftChild B h r) =
      weight (R.signedWeights h.1.1.1) (R.leftParent B h r) -
        weight (R.signedWeights h.1.1.1) (R.firstLeftChild B h r) :=
    weight_complement _ (R.firstLeftChild_subset_parent B hr)
  have hr2 : weight (R.signedWeights h.1.1.1) (R.secondRightChild B h r) =
      weight (R.signedWeights h.1.1.1) (R.rightParent B h r) -
        weight (R.signedWeights h.1.1.1) (R.firstRightChild B h r) :=
    weight_complement _ (R.firstRightChild_subset_parent B hr)
  simpa only [ActualFilters, hl2, hr2, R.leftParent_weight B hr, R.rightParent_weight B hr,
    R.firstLeftChild_weight B hr, R.firstRightChild_weight B hr] using hc

def ActualRepresentation (B : BackgroundAssignment n) (h : R.TrialHistory) : Prop :=
  mixerSpreadTest (R.signedWeights h.1.1.1.1) (R.orderedMixers h.1.1.1.1) n ∧
  (Disjoint (R.leftParent B h.1 h.2) (R.rightParent B h.1 h.2) ∧
    R.leftParent B h.1 h.2 ∪ R.rightParent B h.1 h.2 = h.1.1.1.1.2) ∧
  (weight (R.signedWeights h.1.1.1.1) (R.leftParent B h.1 h.2) +
    weight (R.signedWeights h.1.1.1.1) (R.rightParent B h.1 h.2) =
      R.signedTarget h.1.1.1.1) ∧
  (∀ i, R.chosenMasks (R.actualOffsets B) h.1 h.2 i ⊆ R.selectedHalves h.1.1.1.1 i ∧
    (R.chosenMasks (R.actualOffsets B) h.1 h.2 i).card = (h.1.1.1.2 i).val ∧
    (∃ hsub : R.chosenMasks (R.actualOffsets B) h.1 h.2 i ⊆ R.selectedHalves h.1.1.1.1 i,
      representativePrescriptions hsub (R.selectedHalves_subset h.1.1.1.1 i)
        (representativeBlockProfile (blockCount i) (blockHalf n i) (h.1.1.1.2 i).val)
        (h.1.1.2 i))) ∧
  R.ActualFilters B h.1 h.2

theorem successful_actualRepresentation (B : BackgroundAssignment n) {h : R.TrialHistory}
    (hh : R.Successful (R.actualOffsets B) h) : R.ActualRepresentation B h := by
  refine ⟨R.successful_spread _ hh, R.parents_partition B hh.2, ?_, ?_,
    R.actualFilters_of_hits B hh.2⟩
  · rw [R.leftParent_weight B hh.2, R.rightParent_weight B hh.2]
    ring
  · intro i
    have hm := R.chosenMasks_spec (R.actualOffsets B) hh.2 i
    exact ⟨hm.1, hm.2.1, hm.2.2.2⟩

/-- The actual parent subsets represent the fixed signed solution, meet
the prescribed smaller/complementary mask counts, and pass all six filters. -/
theorem actualRepresentation_probability (B : BackgroundAssignment n)
    (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize)) :
    1 / (inputScale R.input : ℝ) ^ 100 ≤
      R.trialLaw.probability (R.ActualRepresentation B) :=
  (R.successful_probability (R.actualOffsets B) hn hmean hden).trans
    (R.trialLaw.probability_mono (fun _ hh => R.successful_actualRepresentation B hh))

/-- Subtract the unconditional resource failure only after fixing the
representation event; no division by its rare probability is made. -/
theorem actualRepresentation_with_resources (B : BackgroundAssignment n)
    (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (E : R.TrialHistory → Prop) {δ : ℝ}
    (hfail : R.trialLaw.probability (fun h => ¬ E h) ≤ δ) :
    1 / (inputScale R.input : ℝ) ^ 100 - δ ≤
      R.trialLaw.probability (fun h => R.ActualRepresentation B h ∧ E h) :=
  (sub_le_sub (R.actualRepresentation_probability B hn hmean hden) hfail).trans
    (R.trialLaw.probability_inter_ge_sub (R.ActualRepresentation B) E)

end LowSpaceSubsetSum.RepresentationSetup

namespace LowSpaceSubsetSum

theorem eventually_actual_representation :
    ∃ N : ℕ, ∀ n ≥ N, ∀ R : RepresentationSetup n,
      meanDeficiency R.originalWeights Finset.univ R.halfSize <
        (153 / 20000 : ℝ) * n →
      ∀ B : RepresentationSetup.BackgroundAssignment n,
        1 / (inputScale R.input : ℝ) ^ 100 ≤
          R.trialLaw.probability (R.ActualRepresentation B) := by
  obtain ⟨N, hN⟩ := eventually_representation_survival
  refine ⟨N, ?_⟩
  intro n hn R hmean B
  exact (hN n hn R hmean (R.actualOffsets B)).trans
    (R.trialLaw.probability_mono (fun _ hh => R.successful_actualRepresentation B hh))

end LowSpaceSubsetSum

end

end OAI
