import OAI.Combinatorics.Ryser.Construction.DeletionIntersection

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [instFintypeG : Fintype G] [Fintype k] [Fintype F]
variable [instDecidableEqG : DecidableEq G] [DecidableEq k] [DecidableEq F]

def DeletionSeparated (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Prop :=
  ∀ i j : G, i ≠ j → ∀ p ∈ placedSubplane σ (M i) (b i),
    ∀ y ∈ (retainedPoints a).image (placedPoint σ (M j) (b j)),
      ∀ d ∈ alteredDirections σ (M j), projection d p ≠ projection d y

def allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.biUnion (fun i => deletedLines σ (M i) (b i) a)

def deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset (AffineLine F) :=
  (allDeletedLines σ M b a).filter (fun ell => Incidence p ell)

def activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset G :=
  Finset.univ.filter (fun i => ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell)

@[simp] theorem mem_allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ allDeletedLines σ M b a ↔ ∃ i, ell ∈ deletedLines σ (M i) (b i) a := let _ := instDecidableEqG; by
  simp only [allDeletedLines, Finset.mem_biUnion, Finset.mem_univ, true_and]

@[simp] theorem mem_deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (ell : AffineLine F) :
    ell ∈ deletedPencil σ M b a p ↔
      ell ∈ allDeletedLines σ M b a ∧ Incidence p ell := let _ := instDecidableEqG; by
  simp only [deletedPencil, Finset.mem_filter]

@[simp] theorem mem_activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (i : G) :
    i ∈ activeDeletionGroups σ M b a p ↔
      ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell := let _ := instDecidableEqG; by
  simp only [activeDeletionGroups, Finset.mem_filter, Finset.mem_univ, true_and]

theorem not_incidence_deletedLines_of_mem_other_subplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j)
    {p : Point F} (hp : p ∈ placedSubplane σ (M i) (b i))
    {ell : AffineLine F} (hell : ell ∈ deletedLines σ (M j) (b j) a) :
    ¬Incidence p ell := let _ := instFintypeG; let _ := instDecidableEqG; by
  obtain ⟨hdir, y, hy, hyell⟩ := (mem_deletedLines σ (M j) (b j) a ell).mp hell
  have hyplaced : placedPoint σ (M j) (b j) y ∈
      (retainedPoints a).image (placedPoint σ (M j) (b j)) :=
    Finset.mem_image.mpr ⟨y, hy, rfl⟩
  intro hpell
  exact hsep i j hij p hp (placedPoint σ (M j) (b j) y) hyplaced ell.1 hdir
    (hpell.trans hyell.symm)

theorem disjoint_deletedLines_of_separated
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j) :
    Disjoint (deletedLines σ (M i) (b i) a) (deletedLines σ (M j) (b j) a) := by
  apply Finset.disjoint_left.mpr
  intro ell helli hellj
  obtain ⟨y, _, hyell⟩ := ((mem_deletedLines σ (M i) (b i) a ell).mp helli).2
  have hyplane : placedPoint σ (M i) (b i) y ∈ placedSubplane σ (M i) (b i) :=
    (mem_placedSubplane_iff σ (M i) (b i) _).mpr ⟨y, rfl⟩
  exact not_incidence_deletedLines_of_mem_other_subplane
    σ M b a hsep hij hyplane hellj hyell

end RyserCoveringCounterexample.Construction

end

end OAI
