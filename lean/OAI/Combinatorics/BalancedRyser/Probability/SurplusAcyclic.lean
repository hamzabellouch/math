import OAI.Combinatorics.BalancedRyser.Local.LocalCoverMarking
import OAI.Combinatorics.BalancedRyser.Probability.ForwardDependencyExtraction

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped Classical

theorem exists_acyclic_subset_finset {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (k t : ℕ)
    (hloop : ∀ x ∈ S, ¬ R x x)
    (hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ k)
    (hsize : (k + 1) * (t - 1) < S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = t ∧
      WellFounded (fun x y : {x // x ∈ T} => R x.val y.val) := by
  let e := Fintype.equivFin {x // x ∈ S}
  let g : Fin (Fintype.card {x // x ∈ S}) → α := fun j => (e.symm j).val
  have hg : Function.Injective g := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let R' := fun i j => R (g i) (g j)
  have hloop' : ∀ i, ¬ R' i i := fun i => hloop (g i) (e.symm i).property
  have hdegree' : ∀ i, (Finset.univ.filter (R' i)).card ≤ k := by
    intro i
    have hmap : (Finset.univ.filter (R' i)).image g ⊆ S.filter (R (g i)) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨(e.symm j).property, (Finset.mem_filter.mp hj).2⟩
    have hc := Finset.card_image_of_injective (Finset.univ.filter (R' i)) hg
    rw [← hc]
    exact (Finset.card_le_card hmap).trans (hdegree (g i) (e.symm i).property)
  obtain ⟨V, hVcard, hforward⟩ :=
    ForwardDependencyExtraction.exists_forward_subset R' hloop' hdegree'
      (by simpa using hsize)
  obtain ⟨W, hWV, hWcard⟩ := Finset.exists_subset_card_eq hVcard
  let T := W.image g
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact (e.symm j).property
  have hTcard : T.card = t := by
    change (W.image g).card = t
    rw [Finset.card_image_of_injective _ hg, hWcard]
  let rank : {x // x ∈ T} → Fin (Fintype.card {x // x ∈ S}) :=
    fun x => e ⟨x.val, hTS x.property⟩
  have hrank : ∀ x, rank x ∈ W := by
    intro x
    obtain ⟨j, hj, hgx⟩ := Finset.mem_image.mp x.property
    have heq : rank x = j := by
      apply e.symm.injective
      apply Subtype.ext
      simpa only [rank, Equiv.symm_apply_apply] using hgx.symm
    rwa [heq]
  refine ⟨T, hTS, hTcard, ?_⟩
  apply (measure (fun x : {x // x ∈ T} => (rank x).val)).wf.mono
  intro x y hxy
  apply hforward (rank x) (hWV (hrank x)) (rank y) (hWV (hrank y))
  simpa only [R', g, rank, Equiv.symm_apply_apply] using hxy

theorem source_surplus_acyclic {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (b κ : ℕ)
    (hb : 3 ≤ b) (hκ : κ ≤ 1)
    (hcard : 2 * b + 2 - 4 * κ ≤ S.card)
    (hloop : ∀ x ∈ S, ¬ R x x)
    (hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ 2) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = 3 - κ ∧
      WellFounded (fun x y : {x // x ∈ T} => R x.val y.val) := by
  exact exists_acyclic_subset_finset S R 2 (3 - κ) hloop hdegree (by omega)

end
end Balanced.Local.Surplus

end OAI
