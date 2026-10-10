import OAI.Combinatorics.Ryser.Construction.DeletionLines
import OAI.Combinatorics.Ryser.Construction.PlacementIntersection

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [instDecidableEqk : DecidableEq k] [DecidableEq F]

def placedSubplane (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) :
    Finset (Point F) := Finset.univ.image (placedPoint σ M b)

@[simp] theorem mem_placedSubplane_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b p : Point F) : p ∈ placedSubplane σ M b ↔ p ∈ Set.range (placedPoint σ M b) := let _ := instFintypeF; let _ := instDecidableEqk; by
  simp only [placedSubplane, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

theorem card_placedSubplane (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) :
    (placedSubplane σ M b).card = Fintype.card k ^ 2 := let _ := instFintypeF; let _ := instDecidableEqk; by
  unfold placedSubplane
  rw [Finset.card_image_of_injective _ (placedPoint_injective σ M b), Finset.card_univ]
  change Fintype.card (k × k) = Fintype.card k ^ 2
  rw [Fintype.card_prod, pow_two]

theorem exists_placedLine_of_mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    ∃ l : AffineLine k, placedLine σ M b l = ell := by
  have hmem : ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
    simpa only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and] using hell
  obtain ⟨t, _, ht⟩ := (mem_alteredDirections_iff σ M ell.1).mp hmem.1
  obtain ⟨y, _, hy⟩ := hmem.2
  refine ⟨(some t, projection (some t) y), ?_⟩
  exact (eq_placedLine_of_direction_of_incidence σ M b y (some t) ell ht.symm hy).symm

theorem eq_deletedLine_of_incident_of_notMem_placedSubplane
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    {p : Point F} {ell m : AffineLine F}
    (houtside : p ∉ placedSubplane σ M b)
    (hell : ell ∈ deletedLines σ M b a) (hm : m ∈ deletedLines σ M b a)
    (hpell : Incidence p ell) (hpm : Incidence p m) : ell = m := by
  have hout : p ∉ Set.range (placedPoint σ M b) := by
    simpa only [mem_placedSubplane_iff] using houtside
  obtain ⟨l, rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hell
  obtain ⟨l', rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hm
  exact eq_placedLine_of_incident_of_notMem_range σ M b hout hpell hpm

theorem card_deletedLines_through_le_one (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (p : Point F)
    (houtside : p ∉ placedSubplane σ M b) :
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro ell hell m hm
  obtain ⟨helld, hpell⟩ := Finset.mem_filter.mp hell
  obtain ⟨hmd, hpm⟩ := Finset.mem_filter.mp hm
  exact eq_deletedLine_of_incident_of_notMem_placedSubplane
    σ M b a houtside helld hmd hpell hpm

end RyserCoveringCounterexample.Construction

end

end OAI
