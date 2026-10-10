import OAI.Combinatorics.Ryser.Construction.PlacedLines
import OAI.Combinatorics.Ryser.Construction.DirectionSets
import OAI.Combinatorics.Ryser.Construction.GadgetDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [DecidableEq k] [DecidableEq F]

def OriginalLineDensity (a : GadgetOutcome k) : Prop :=
  ∀ t : NonzeroSlope k, ∀ c : k, c ≠ a t →
    5 ≤ ((retainedPoints a).filter (fun p => Incidence p (some t.val, c))).card

def deletedLines (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.filter (fun ell => ell.1 ∈ alteredDirections σ M ∧
    ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell)

@[simp] theorem mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ deletedLines σ M b a ↔ ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
  simp only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and]

theorem intercept_ne_omitted_of_mem_retained (a : GadgetOutcome k)
    (t : NonzeroSlope k) {p : Point k} {c : k}
    (hp : p ∈ retainedPoints a) (hpc : Incidence p (some t.val, c)) :
    c ≠ a t := by
  intro hc
  apply not_incidence_omittedLine a hp t
  simpa only [omittedLine, hc] using hpc

theorem deletedLines_direction_eq_image (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    (deletedLines σ M b a).filter
        (fun ell => ell.1 = placedDirection σ M (some t.val)) =
      (Finset.univ.erase (a t)).image
        (fun c : k => placedLine σ M b (some t.val, c)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hdel, hdir⟩ := Finset.mem_filter.mp hell
    obtain ⟨y, hy, hyell⟩ := ((mem_deletedLines σ M b a ell).mp hdel).2
    have hline : ell = placedLine σ M b
        (some t.val, projection (some t.val) y) :=
      eq_placedLine_of_direction_of_incidence σ M b y (some t.val) ell hdir hyell
    have hc : projection (some t.val) y ≠ a t :=
      intercept_ne_omitted_of_mem_retained a t hy rfl
    exact Finset.mem_image.mpr
      ⟨projection (some t.val) y, Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩,
        hline.symm⟩
  · intro hell
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hell
    have hpos : 0 < ((retainedPoints a).filter
        (fun p => Incidence p (some t.val, c))).card :=
      lt_of_lt_of_le (by decide : 0 < 5) (ha t c (Finset.mem_erase.mp hc).1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    obtain ⟨hyret, hyline⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨(mem_deletedLines σ M b a _).mpr ?_, rfl⟩
    exact ⟨placedDirection_mem_alteredDirections σ M t.val t.property,
      y, hyret, (incidence_placedLine_iff σ M b y _).mpr hyline⟩

theorem card_deletedLines_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    ((deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t.val))).card =
        Fintype.card k - 1 := by
  have hinj : Function.Injective
      (fun c : k => placedLine σ M b (some t.val, c)) := by
    intro c c' h
    exact congrArg Prod.snd (placedLine_injective σ M b h)
  rw [deletedLines_direction_eq_image σ M b a ha t,
    Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ (a t)), Finset.card_univ]

theorem card_deletedLines_of_mem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card =
      Fintype.card k - 1 := by
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  exact card_deletedLines_direction σ M b a ha ⟨t, ht⟩

theorem card_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    (deletedLines σ M b a).card = (Fintype.card k - 1) ^ 2 := by
  calc
    (deletedLines σ M b a).card =
        ∑ d ∈ alteredDirections σ M,
          ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun ell hell => ((mem_deletedLines σ M b a ell).mp hell).1)
    _ = (alteredDirections σ M).card * (Fintype.card k - 1) :=
      Finset.sum_const_nat (fun d hd =>
        card_deletedLines_of_mem_alteredDirections σ M b a ha d hd)
    _ = (Fintype.card k - 1) ^ 2 := by rw [card_alteredDirections, pow_two]

theorem card_placedRetained_incident_placedLine (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (l : AffineLine k) :
    (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p (placedLine σ M b l))).card =
        ((retainedPoints a).filter (fun p => Incidence p l)).card := let _ := instFintypeF; by
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (placedPoint_injective σ M b)]
  congr 1
  ext p
  simp only [Finset.mem_filter, incidence_placedLine_iff]

theorem deletedLine_many_placedRetainedPoints (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    5 ≤ (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p ell)).card := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M ell.1).mp
    ((mem_deletedLines σ M b a ell).mp hell).1
  have hfiber : ell ∈ (deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t)) :=
    Finset.mem_filter.mpr ⟨hell, htd.symm⟩
  rw [deletedLines_direction_eq_image σ M b a ha ⟨t, ht⟩] at hfiber
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hfiber
  rw [card_placedRetained_incident_placedLine]
  exact ha ⟨t, ht⟩ c (Finset.mem_erase.mp hc).1

end RyserCoveringCounterexample.Construction

end

end OAI
