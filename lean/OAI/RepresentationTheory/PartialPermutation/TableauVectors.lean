import Mathlib
import OAI.RepresentationTheory.PartialPermutation.StandardTableaux
import OAI.RepresentationTheory.PartialPermutation.Polytabloids
import OAI.RepresentationTheory.PartialPermutation.ColumnRearrangement

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

abbrev Std (μ : YoungDiagram) := Tableau.StandardFilling μ.cells

def referenceLabels (μ : YoungDiagram) : μ.cells ≃ Fin (Fintype.card μ.cells) := Fintype.equivFin _
def tableauPerm (μ : YoungDiagram) (t : Std μ) : Equiv.Perm μ.cells :=
  t.1.trans (referenceLabels μ).symm
def tableauTabloid (μ : YoungDiagram) (t : Std μ) : Tabloid μ :=
  relabel μ (tableauPerm μ t) (canonical μ)
def tableauVector (μ : YoungDiagram) (t : Std μ) : EuclideanSpace ℂ (Tabloid μ) :=
  tabloidRep μ (tableauPerm μ t) (polytabloid μ)

def rowCell (μ : YoungDiagram) (i : ℕ) (j : Fin (μ.rowLen i)) : μ.cells :=
  ⟨(i,j),μ.mem_iff_lt_rowLen.mpr j.2⟩

lemma rowCell_strictMono (μ : YoungDiagram) (i : ℕ) : StrictMono (rowCell μ i) := by
  intro j k h
  apply lt_of_le_of_ne
  · exact ⟨le_refl _,h.le⟩
  · intro he
    exact h.ne (Fin.ext (congrArg (fun x : μ.cells => x.1.2) he))

lemma standard_eq_of_inverse_rows (μ : YoungDiagram) (s t : Std μ)
    (h : ∀ k, row μ (s.1.symm k)=row μ (t.1.symm k)) : s=t := by
  have hh (i : ℕ) : (fun j => s.1 (rowCell μ i j))=(fun j => t.1 (rowCell μ i j)) := by
    apply ((s.2.comp (rowCell_strictMono μ i)).range_inj_of_wellFoundedLT
      (t.2.comp (rowCell_strictMono μ i))).mp
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      let x := t.1.symm (s.1 (rowCell μ i j))
      have hx : row μ x=i := by simpa [x,rowCell,row] using (h (s.1 (rowCell μ i j))).symm
      refine ⟨⟨col μ x,?_⟩,?_⟩
      · have hc := μ.mem_iff_lt_rowLen.mp x.2
        simpa only [← hx,row,col] using hc
      · have he : rowCell μ i ⟨col μ x,by simpa only [← hx,row,col] using μ.mem_iff_lt_rowLen.mp x.2⟩=x :=
          cell_eq_of_row_col μ hx.symm rfl
        simp only [Function.comp_apply]
        rw [he]
        exact t.1.apply_symm_apply _
    · rintro ⟨j,rfl⟩
      let x := s.1.symm (t.1 (rowCell μ i j))
      have hx : row μ x=i := by simpa [x,rowCell,row] using h (t.1 (rowCell μ i j))
      refine ⟨⟨col μ x,?_⟩,?_⟩
      · have hc := μ.mem_iff_lt_rowLen.mp x.2
        simpa only [← hx,row,col] using hc
      · have he : rowCell μ i ⟨col μ x,by simpa only [← hx,row,col] using μ.mem_iff_lt_rowLen.mp x.2⟩=x :=
          cell_eq_of_row_col μ hx.symm rfl
        simp only [Function.comp_apply]
        rw [he]
        exact s.1.apply_symm_apply _
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrFun (hh (row μ x)) ⟨col μ x,μ.mem_iff_lt_rowLen.mp x.2⟩

lemma tableauTabloid_injective (μ : YoungDiagram) : Function.Injective (tableauTabloid μ) := by
  intro s t h
  apply standard_eq_of_inverse_rows μ s t
  intro k
  have hh := congrFun (congrArg Subtype.val h) ((referenceLabels μ).symm k)
  simpa [tableauTabloid,tableauPerm,relabel,canonical,ofPerm] using hh

def score (μ : YoungDiagram) (r : Tabloid μ) : ℕ :=
  ∑ x, ((referenceLabels μ) x).val * r.1 x

lemma score_relabel (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ) :
    score μ (relabel μ g r) = ∑ x, ((referenceLabels μ) (g x)).val * r.1 x := by
  unfold score
  exact (Fintype.sum_equiv g _ _ (fun x => by simp only [relabel_apply,
    Equiv.Perm.inv_def,Equiv.symm_apply_apply])).symm

lemma score_tableau_column (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ) :
    score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) =
      ∑ x, (t.1 x).val * row μ (c.1⁻¹ x) := by
  rw [score_relabel]
  apply Finset.sum_congr rfl
  intro x _
  simp [tableauPerm,relabel,canonical,ofPerm]

lemma score_tableau (μ : YoungDiagram) (t : Std μ) :
    score μ (tableauTabloid μ t)=∑ x, (t.1 x).val * row μ x := by
  simpa only [relabel_one,Subgroup.coe_one,inv_one,Equiv.Perm.one_apply,tableauTabloid]
    using score_tableau_column μ t 1

lemma score_column_le (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ) :
    score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) ≤
      score μ (tableauTabloid μ t) := by
  rw [score_tableau_column,score_tableau]
  exact full_rearrangement μ _ (fun x y h => t.2 h) c⁻¹

lemma score_column_eq (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ)
    (h : score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) =
      score μ (tableauTabloid μ t)) : c=1 := by
  rw [score_tableau_column,score_tableau] at h
  have hh := full_rearrangement_eq μ _ (fun x y h => t.2 h) c⁻¹ h
  simpa using hh

end
end PartialPermutation.YoungTabloid
end

end OAI
