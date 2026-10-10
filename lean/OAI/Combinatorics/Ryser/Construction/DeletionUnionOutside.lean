import OAI.Combinatorics.Ryser.Construction.DeletionUnionBasic

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

def activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) : AffineLine F :=
  Classical.choose ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_spec (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a ∧
      Incidence p (activeDeletionLine σ M b a p i) :=
  Classical.choose_spec ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_mem (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a :=
  (activeDeletionLine_spec σ M b a p i).1

theorem incidence_activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    Incidence p (activeDeletionLine σ M b a p i) :=
  (activeDeletionLine_spec σ M b a p i).2

theorem activeDeletionLine_injective (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (hsep : DeletionSeparated σ M b a) :
    Function.Injective (activeDeletionLine σ M b a p) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hdisj := disjoint_deletedLines_of_separated σ M b a hsep hne
  have hmemj : activeDeletionLine σ M b a p i ∈
      deletedLines σ (M j.val) (b j.val) a := by
    rw [hij]
    exact activeDeletionLine_mem σ M b a p j
  exact (Finset.disjoint_left.mp hdisj)
    (activeDeletionLine_mem σ M b a p i) hmemj

def activeDeletionLineInPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    {ell // ell ∈ deletedPencil σ M b a p} :=
  ⟨activeDeletionLine σ M b a p i,
    (mem_deletedPencil σ M b a p _).mpr
      ⟨(mem_allDeletedLines σ M b a _).mpr
        ⟨i.val, activeDeletionLine_mem σ M b a p i⟩,
        incidence_activeDeletionLine σ M b a p i⟩⟩

theorem activeDeletionLineInPencil_surjective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Surjective (activeDeletionLineInPencil σ M b a p) := by
  intro ell
  obtain ⟨hell, hpell⟩ := (mem_deletedPencil σ M b a p ell.val).mp ell.property
  obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell.val).mp hell
  have hactive : i ∈ activeDeletionGroups σ M b a p :=
    (mem_activeDeletionGroups σ M b a p i).mpr ⟨ell.val, hi, hpell⟩
  refine ⟨⟨i, hactive⟩, ?_⟩
  apply Subtype.ext
  change activeDeletionLine σ M b a p ⟨i, hactive⟩ = ell.val
  exact eq_deletedLine_of_incident_of_notMem_placedSubplane
    σ (M i) (b i) a (hout i)
    (activeDeletionLine_mem σ M b a p ⟨i, hactive⟩) hi
    (incidence_activeDeletionLine σ M b a p ⟨i, hactive⟩) hpell

theorem activeDeletionLineInPencil_bijective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Bijective (activeDeletionLineInPencil σ M b a p) := by
  constructor
  · intro i j hij
    exact activeDeletionLine_injective σ M b a p hsep (congrArg Subtype.val hij)
  · exact activeDeletionLineInPencil_surjective σ M b a p hout

def activeDeletionGroupEquivDeletedPencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    {i // i ∈ activeDeletionGroups σ M b a p} ≃
      {ell // ell ∈ deletedPencil σ M b a p} :=
  Equiv.ofBijective (activeDeletionLineInPencil σ M b a p)
    (activeDeletionLineInPencil_bijective σ M b a p hsep hout)

theorem card_deletedPencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card = (activeDeletionGroups σ M b a p).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (activeDeletionGroupEquivDeletedPencil σ M b a p hsep hout)).symm

theorem deletedPencil_eq_inter_affinePencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) :
    deletedPencil σ M b a p = allDeletedLines σ M b a ∩ affinePencil (Sum.inl p) := by
  ext ell
  simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
    projectiveIncidence_finite_affine]

theorem card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inl p)).card =
      (activeDeletionGroups σ M b a p).card := by
  rw [← deletedPencil_eq_inter_affinePencil σ M b a p]
  exact card_deletedPencil_eq_card_activeDeletionGroups σ M b a p hsep hout

theorem activeDeletionLine_many_placedRetainedPoints
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (ha : OriginalLineDensity a)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    5 ≤ (((retainedPoints a).image (placedPoint σ (M i.val) (b i.val))).filter
      (fun q => Incidence q (activeDeletionLine σ M b a p i))).card :=
  deletedLine_many_placedRetainedPoints σ (M i.val) (b i.val) a ha
    (activeDeletionLine_mem σ M b a p i)

end RyserCoveringCounterexample.Construction

end

end OAI
