import OAI.Probability.FirstPassage.BKFamilies
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma upward_disjointOccurrence (s : Finset α) (A B : Finset (Finset α)) :
    UpwardFamily s (disjointOccurrenceFamily s A B) := by
  constructor
  · intro x hx
    exact ((mem_disjointOccurrenceFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hys,a,ha,b,hb,hax.trans hxy,hbx.trans hxy,hab⟩

noncomputable def fairFamilyMass (s : Finset α) (A : Finset (Finset α)) : ℝ :=
  A.card / (2:ℝ)^s.card

omit [DecidableEq α] in
lemma fairFamilyMass_nonneg (s : Finset α) (A : Finset (Finset α)) :
    0 ≤ fairFamilyMass s A := by unfold fairFamilyMass; positivity

omit [DecidableEq α] in
lemma fairFamilyMass_mono (s : Finset α) {A B : Finset (Finset α)} (h : A ⊆ B) :
    fairFamilyMass s A ≤ fairFamilyMass s B := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

omit [DecidableEq α] in
lemma fairFamilyMass_powerset (s : Finset α) : fairFamilyMass s s.powerset = 1 := by
  simp [fairFamilyMass,Finset.card_powerset]

lemma finite_fair_BK_mass (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    fairFamilyMass s (disjointOccurrenceFamily s A B) ≤ fairFamilyMass s A * fairFamilyMass s B := by
  have h := finite_fair_BK s A B hA hB
  have hr : (2:ℝ)^s.card * (disjointOccurrenceFamily s A B).card ≤ (A.card:ℝ)*B.card := by
    exact_mod_cast h
  unfold fairFamilyMass
  rw [div_mul_div_comm,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) s.card]

noncomputable def iteratedDisjointOccurrence (s : Finset α) : List (Finset (Finset α)) → Finset (Finset α)
  | [] => s.powerset
  | A :: As => disjointOccurrenceFamily s A (iteratedDisjointOccurrence s As)

lemma upward_iteratedDisjointOccurrence (s : Finset α) (As : List (Finset (Finset α))) :
    UpwardFamily s (iteratedDisjointOccurrence s As) := by
  cases As with
  | nil =>
    constructor
    · intro x hx; exact mem_powerset.mp hx
    · intro x hx y hxy hys; exact mem_powerset.mpr hys
  | cons A As => exact upward_disjointOccurrence s A _

theorem finite_fair_BK_repeated (s : Finset α) (As : List (Finset (Finset α)))
    (hAs : ∀ A ∈ As, UpwardFamily s A) :
    fairFamilyMass s (iteratedDisjointOccurrence s As) ≤ (As.map (fairFamilyMass s)).prod := by
  induction As with
  | nil => simp [iteratedDisjointOccurrence,fairFamilyMass_powerset]
  | cons A As ih =>
    have hA := hAs A (List.mem_cons_self ..)
    have htail : ∀ B ∈ As, UpwardFamily s B := fun B hB => hAs B (List.mem_cons_of_mem _ hB)
    exact (finite_fair_BK_mass s A _ hA (upward_iteratedDisjointOccurrence s As)).trans
      (by simpa using mul_le_mul_of_nonneg_left (ih htail) (fairFamilyMass_nonneg s A))

lemma mem_foldr_union (ws : List (Finset α)) (a : α) :
    a ∈ ws.foldr (· ∪ ·) ∅ ↔ ∃ v ∈ ws, a ∈ v := by
  induction ws with
  | nil => simp
  | cons v vs ih => simp [ih]

theorem certificates_mem_iterated (s : Finset α) (As : List (Finset (Finset α)))
    (ws : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hmem : List.Forall₂ (fun w A => w ∈ A) ws As)
    (hdis : ws.Pairwise Disjoint) (hsub : ∀ w ∈ ws, w ⊆ x) :
    x ∈ iteratedDisjointOccurrence s As := by
  induction hmem generalizing x with
  | nil => exact mem_powerset.mpr hxs
  | @cons w A ws As hw hmem ih =>
    have hd := List.pairwise_cons.mp hdis
    let u : Finset α := ws.foldr (· ∪ ·) ∅
    have hu : ∀ a, a ∈ u ↔ ∃ v ∈ ws, a ∈ v := mem_foldr_union ws
    have hux : u ⊆ x := by
      intro a ha
      obtain ⟨v,hv,hav⟩ := (hu a).mp ha
      exact hsub v (List.mem_cons_of_mem _ hv) hav
    have htail : ∀ v ∈ ws, v ⊆ u := by
      intro v hv a ha
      exact (hu a).mpr ⟨v,hv,ha⟩
    have hwu : Disjoint w u := by
      apply Finset.disjoint_left.mpr
      intro a haw hau
      obtain ⟨v,hv,hav⟩ := (hu a).mp hau
      exact Finset.disjoint_left.mp (hd.1 v hv) haw hav
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hxs,w,hw,u,
      ih u (hux.trans hxs) hd.2 htail,hsub w (List.mem_cons_self ..),hux,hwu⟩

noncomputable def certifiedDisjointFamily (s : Finset α) (As : List (Finset (Finset α))) :
    Finset (Finset α) := by
  classical
  exact s.powerset.filter (fun x => ∃ ws : List (Finset α),
    List.Forall₂ (fun w A => w ∈ A) ws As ∧ ws.Pairwise Disjoint ∧ ∀ w ∈ ws, w ⊆ x)

theorem finite_fair_BK_certificates (s : Finset α) (As : List (Finset (Finset α)))
    (hAs : ∀ A ∈ As, UpwardFamily s A) :
    fairFamilyMass s (certifiedDisjointFamily s As) ≤ (As.map (fairFamilyMass s)).prod := by
  apply (fairFamilyMass_mono s ?_).trans (finite_fair_BK_repeated s As hAs)
  intro x hx
  simp only [certifiedDisjointFamily,mem_filter,mem_powerset] at hx
  obtain ⟨hxs,ws,hmem,hdis,hsub⟩ := hx
  exact certificates_mem_iterated s As ws x hxs hmem hdis hsub

end PlanarFPP

end OAI
