import OAI.Probability.MatroidProphet.Pivots.Basic
import OAI.Probability.MatroidProphet.Pivots.GreedyScan

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma kept_label_injOn
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    Set.InjOn label (keptOccurrences M label time : Set β) := by
  classical
  have hd : ∀ x y, x ∈ keptOccurrences M label time → y ∈ keptOccurrences M label time →
      time x < time y → label x ≠ label y := by
    intro x y _ hy hxy hlabels
    apply (Finset.mem_filter.mp hy).2
    rw [← hlabels]
    exact M.mem_closure_of_mem ⟨x, hxy, rfl⟩ (by rintro _ ⟨z, _, rfl⟩; exact hground z)
  intro x hx y hy hlabels
  apply htime
  rcases lt_trichotomy (time x) (time y) with hlt | heq | hgt
  · exact False.elim (hd x y hx hy hlt hlabels)
  · exact heq
  · exact False.elim (hd y x hy hx hgt hlabels.symm)

noncomputable def occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) : Finset β := by
  classical
  exact J.filter (fun o => label o ∈ support M (label '' (J : Set β)) e)

lemma mem_occurrenceSupport
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    {M : Matroid α} {label : β → α} {J : Finset β} {e : α} {o : β} :
    o ∈ occurrenceSupport M label J e ↔
      o ∈ J ∧ label o ∈ support M (label '' (J : Set β)) e := by
  classical
  simp [occurrenceSupport]

lemma mem_closure_iff_occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) (hI : M.Indep (label '' (J : Set β)))
    (he : e ∈ M.closure (label '' (J : Set β)))
    (hinj : Set.InjOn label (J : Set β)) (P : β → Prop) :
    e ∈ M.closure (label '' {o | o ∈ J ∧ P o}) ↔
      ∀ o ∈ occurrenceSupport M label J e, P o := by
  classical
  rw [mem_closure_iff_support_subset hI he (by
    rintro _ ⟨o, ⟨ho, _⟩, rfl⟩; exact ⟨o, ho, rfl⟩)]
  constructor
  · intro h o ho
    obtain ⟨hoJ, hol⟩ := mem_occurrenceSupport.mp ho
    obtain ⟨p, ⟨hpJ, hpP⟩, hp⟩ := h hol
    exact (hinj hpJ hoJ hp) ▸ hpP
  · intro h x hx
    obtain ⟨o, ho, rfl⟩ := support_subset he hx
    exact ⟨o, ⟨ho, h o (mem_occurrenceSupport.mpr ⟨ho, hx⟩)⟩, rfl⟩

def IsPivot (M : Matroid α) (label : β → α) (time : β → ℕ) (e : α) (o : β) : Prop :=
  e ∈ M.closure (label '' {p | time p ≤ time o}) ∧
    e ∉ M.closure (label '' {p | time p < time o})

lemma pivot_mem_support_and_max (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time)
    {e : α} {o : β} (hpivot : IsPivot M label time e o) :
    o ∈ occurrenceSupport M label (keptOccurrences M label time) e ∧
      ∀ p ∈ occurrenceSupport M label (keptOccurrences M label time) e, time p ≤ time o := by
  classical
  let J := keptOccurrences M label time
  have hI := keptOccurrences_indep M label time hground htime
  have hinj := kept_label_injOn M label time hground htime
  have hup : e ∈ M.closure (label '' {p | p ∈ J ∧ time p ≤ time o}) := by
    have h := hpivot.1
    have hcl := greedy_prefix_closure M label time hground (time o + 1)
    simp only [Nat.lt_succ_iff] at hcl
    rw [hcl] at h
    exact h
  have he : e ∈ M.closure (label '' (J : Set β)) := by
    apply M.closure_subset_closure ?_ hup
    rintro _ ⟨p, ⟨hp, _⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hmax := (mem_closure_iff_occurrenceSupport M label J e hI he hinj
    (fun p => time p ≤ time o)).mp hup
  have hnot : ¬ ∀ p ∈ occurrenceSupport M label J e, time p < time o := by
    intro h
    apply hpivot.2
    rw [greedy_prefix_closure M label time hground (time o)]
    exact (mem_closure_iff_occurrenceSupport M label J e hI he hinj
      (fun p => time p < time o)).mpr h
  push Not at hnot
  obtain ⟨p, hp, hge⟩ := hnot
  have heq : p = o := htime (Nat.le_antisymm (hmax p hp) hge)
  exact ⟨heq ▸ hp, hmax⟩

end Pivots
end MatroidProphet

end OAI
