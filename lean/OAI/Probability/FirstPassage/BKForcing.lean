import OAI.Probability.FirstPassage.BKRepeated

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

def ForcesBits (s : Finset α) (A : Finset (Finset α)) (x c : Finset α) : Prop :=
  ∀ y ⊆ s, (∀ e ∈ c, e ∈ y ↔ e ∈ x) → y ∈ A

lemma ForcesBits.positive_certificate {s : Finset α} {A : Finset (Finset α)}
    {x c : Finset α} (hxs : x ⊆ s) (h : ForcesBits s A x c) : x ∩ c ∈ A := by
  apply h (x ∩ c) ((inter_subset_left).trans hxs)
  intro e he
  simp [he]

theorem forcing_certificates_mem (s : Finset α) (As : List (Finset (Finset α)))
    (cs : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hforce : List.Forall₂ (fun c A => ForcesBits s A x c) cs As)
    (hdis : cs.Pairwise Disjoint) : x ∈ iteratedDisjointOccurrence s As := by
  apply certificates_mem_iterated s As (cs.map (fun c => x ∩ c)) x hxs
  · clear hdis
    induction hforce with
    | nil => exact List.Forall₂.nil
    | cons h ht ih => exact List.Forall₂.cons (h.positive_certificate hxs) ih
  · rw [List.pairwise_map]
    exact hdis.imp (fun hab => hab.mono (inter_subset_right) (inter_subset_right))
  · intro w hw
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hw
    exact inter_subset_left

theorem finite_fair_BK_forcing (s : Finset α) (As : List (Finset (Finset α)))
    (D : Finset (Finset α)) (hAs : ∀ A ∈ As, UpwardFamily s A)
    (hD : ∀ x ∈ D, x ⊆ s ∧ ∃ cs : List (Finset α),
      List.Forall₂ (fun c A => ForcesBits s A x c) cs As ∧ cs.Pairwise Disjoint) :
    fairFamilyMass s D ≤ (As.map (fairFamilyMass s)).prod := by
  apply (fairFamilyMass_mono s ?_).trans (finite_fair_BK_repeated s As hAs)
  intro x hx
  obtain ⟨hxs,cs,hforce,hdis⟩ := hD x hx
  exact forcing_certificates_mem s As cs x hxs hforce hdis

end PlanarFPP

end OAI
