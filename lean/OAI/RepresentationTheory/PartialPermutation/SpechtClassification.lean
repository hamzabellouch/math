import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Plancherel
import OAI.RepresentationTheory.PartialPermutation.Equivalences
import OAI.RepresentationTheory.PartialPermutation.SpechtDimension
import OAI.RepresentationTheory.PartialPermutation.SpechtShapes
import OAI.RepresentationTheory.PartialPermutation.ConjugacyCounts
import OAI.RepresentationTheory.PartialPermutation.ClassCharacters

namespace OAI

section
namespace PartialPermutation
namespace SpechtActual
noncomputable section
open YoungTabloid DiagramCounting
open scoped Classical

def labels {n : ℕ} (μ : Shape n) : μ.1.cells ≃ Fin n :=
  (Fintype.equivFin μ.1.cells).trans (finCongr (by simpa using μ.2))

def rep {n : ℕ} (μ : Shape n) :=
  (spechtRep μ.1).comp (labels μ).symm.permCongrHom.toMonoidHom

instance {n : ℕ} (μ : Shape n) : Representation.IsIrreducible (rep μ) := by
  unfold rep
  infer_instance

def index {n : ℕ} (μ : Shape n) : IrreducibleIndex (Equiv.Perm (Fin n)) :=
  (irreducibleRep_complete (rep μ)).choose

lemma index_spec {n : ℕ} (μ : Shape n) :
    Nonempty (Representation.Equiv (irreducibleRep (index μ)) (rep μ)) :=
  (irreducibleRep_complete (rep μ)).choose_spec.1

lemma rep_equiv_shape_eq {n : ℕ} (μ ν : Shape n)
    (E : Representation.Equiv (rep μ) (rep ν)) : μ=ν := by
  apply Subtype.ext
  let e : μ.1.cells ≃ ν.1.cells := (labels μ).trans (labels ν).symm
  apply specht_equiv_shape_eq μ.1 ν.1 e E.toLinearEquiv
  intro g x
  have hh := LinearMap.congr_fun (E.isIntertwining' ((labels μ).permCongrHom g)) x
  change E (spechtRep μ.1 ((labels μ).symm.permCongrHom ((labels μ).permCongrHom g)) x)=
    spechtRep ν.1 ((labels ν).symm.permCongrHom ((labels μ).permCongrHom g)) (E x) at hh
  have he : (labels μ).symm.permCongrHom ((labels μ).permCongrHom g)=g :=
    (labels μ).permCongrHom.symm_apply_apply g
  rw [he] at hh
  exact hh

lemma index_injective (n : ℕ) : Function.Injective (@index n) := by
  intro μ ν h
  obtain ⟨e⟩ := index_spec μ
  obtain ⟨f⟩ := index_spec ν
  apply rep_equiv_shape_eq μ ν
  exact e.symm.trans (h ▸ f)

lemma actual_irreducible_card_le (n : ℕ) :
    Fintype.card (IrreducibleIndex (Equiv.Perm (Fin n))) ≤ Fintype.card (Shape n) := by
  exact (irreducible_family_card_le_conjClasses (fun c => irreducibleSpace c)
    (fun c => irreducibleRep c) (componentRep_equiv_iff (regularRep (Equiv.Perm (Fin n))))).trans
    (symmetric_conjClasses_card_le n)

theorem index_bijective (n : ℕ) : Function.Bijective (@index n) := by
  have hc := actual_irreducible_card_le n
  have hi := index_injective n
  have he := le_antisymm hc (Fintype.card_le_of_injective _ hi)
  exact ⟨hi,(Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,he.symm⟩ |>.surjective⟩

def indexEquiv (n : ℕ) : Shape n ≃ IrreducibleIndex (Equiv.Perm (Fin n)) :=
  Equiv.ofBijective index (index_bijective n)

lemma standardCount_le_degree {n : ℕ} (μ : Shape n) :
    Tableau.standardCount μ.1 ≤ irreducibleDegree (index μ) := by
  obtain ⟨e⟩ := index_spec μ
  have hd := e.toLinearEquiv.finrank_eq
  exact (standardCount_le_specht_degree μ.1).trans_eq hd.symm

end
end SpechtActual
end PartialPermutation

end

end OAI
