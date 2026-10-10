import Mathlib
import OAI.RepresentationTheory.PartialPermutation.SpechtModules
import OAI.RepresentationTheory.PartialPermutation.TableauVectors

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma tableauVector_diag (μ : YoungDiagram) (t : Std μ) :
    tableauVector μ t (tableauTabloid μ t)=1 := by
  change polytabloid μ (relabel μ (tableauPerm μ t)⁻¹
    (relabel μ (tableauPerm μ t) (canonical μ)))=1
  rw [← relabel_mul,inv_mul_cancel,relabel_one,polytabloid_canonical]

lemma polytabloid_support (μ : YoungDiagram) (r : Tabloid μ) (h : polytabloid μ r≠0) :
    ∃ c : columnGroup μ, r=relabel μ c (canonical μ) := by
  apply transversal_column_orbit μ r
  by_contra hr
  exact h (alternating_zero_nontransversal μ _ (polytabloid_alternating μ) r hr)

lemma tableauVector_support (μ : YoungDiagram) (t : Std μ) (r : Tabloid μ)
    (h : tableauVector μ t r≠0) :
    ∃ c : columnGroup μ, r=relabel μ (tableauPerm μ t) (relabel μ c (canonical μ)) := by
  obtain ⟨c,hc⟩ := polytabloid_support μ _ h
  refine ⟨c,?_⟩
  have hh := congrArg (relabel μ (tableauPerm μ t)) hc
  simpa only [← relabel_mul,mul_inv_cancel,relabel_one] using hh

lemma tableauVector_triangular (μ : YoungDiagram) (s t : Std μ)
    (hne : s≠t) (h : tableauVector μ s (tableauTabloid μ t)≠0) :
    score μ (tableauTabloid μ t)<score μ (tableauTabloid μ s) := by
  obtain ⟨c,hc⟩ := tableauVector_support μ s _ h
  have hle := score_column_le μ s c
  rw [← hc] at hle
  apply lt_of_le_of_ne hle
  intro hh
  have h1 := score_column_eq μ s c (hc ▸ hh)
  subst c
  apply hne
  apply tableauTabloid_injective μ
  simpa only [Subgroup.coe_one,relabel_one,tableauTabloid] using hc.symm

lemma triangular_linearIndependent {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (r : ι → α) (k : ι → ℕ)
    (hd : ∀ i, v i (r i)=1) (ht : ∀ i j, i≠j → v i (r j)≠0 → k j<k i) :
    LinearIndependent ℂ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  by_contra hi
  let S := univ.filter (fun j => a j≠0)
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image k ⟨i,by simpa [S] using hi⟩
  have haj : a j≠0 := (mem_filter.mp hj).2
  have hv (l : ι) (hl : l≠j) : a l * v l (r j)=0 := by
    by_cases hla : a l=0
    · simp [hla]
    have hzero : v l (r j)=0 := by
      by_contra hne
      exact (not_lt_of_ge (hmax l (by simp [S,hla]))) (ht l j hl hne)
    simp [hzero]
  have he := congrArg (fun w : EuclideanSpace ℂ α => w (r j)) ha
  have hs : (∑ l, a l * v l (r j))=a j := by
    rw [Finset.sum_eq_single j (fun l _ hl => hv l hl) (fun h => (h (mem_univ j)).elim),hd,mul_one]
  simp at he
  exact haj (hs.symm.trans he)

lemma tableauVector_independent (μ : YoungDiagram) : LinearIndependent ℂ (tableauVector μ) :=
  triangular_linearIndependent _ (tableauTabloid μ) (fun t => score μ (tableauTabloid μ t))
    (tableauVector_diag μ) (tableauVector_triangular μ)

theorem standardCount_le_specht_degree (μ : YoungDiagram) :
    Tableau.standardCount μ ≤ Module.finrank ℂ (spechtSub μ).toSubmodule := by
  let v : Std μ → (spechtSub μ).toSubmodule := fun t =>
    ⟨tableauVector μ t,(spechtSub μ).apply_mem_toSubmodule _ (polytabloid_mem_specht μ)⟩
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp
    (spechtSub μ).toSubmodule.subtype (tableauVector_independent μ)
  exact hv.fintype_card_le_finrank

end
end PartialPermutation.YoungTabloid

end

end OAI
