import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.CompleteUnit

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section
variable {I : Type*} [Fintype I] (A : I → Type*) (e : ∀i,A i → ℤ)

def finitePiReindex : (∀j:Fin (Fintype.card I),A ((Fintype.equivFin I).symm j)) ≃ (∀i,A i) :=
  Equiv.piCongrLeft A (Fintype.equivFin I).symm

lemma finitePiReindex_energy (f : ∀j:Fin (Fintype.card I),A ((Fintype.equivFin I).symm j)) :
    (∑i,e i (finitePiReindex A f i))=∑j,e ((Fintype.equivFin I).symm j) (f j) := by
  rw [←(Fintype.equivFin I).symm.sum_comp (fun i=>e i (finitePiReindex A f i))]
  simp only [finitePiReindex,Equiv.piCongrLeft_apply_apply]

lemma admissible_pi (he : ∀i,Admissible (e i)) : Admissible (fun f : ∀i,A i=>∑i,e i (f i)) :=
  admissible_equiv (admissible_fin_pi (Fintype.card I) _ _ (fun j=>he ((Fintype.equivFin I).symm j)))
    (finitePiReindex A) (finitePiReindex_energy A e)

lemma series_pi (he : ∀i,Admissible (e i)) :
    (∏i,series (e i) (he i))=series (fun f : ∀i,A i=>∑i,e i (f i)) (admissible_pi A e he) := by
  rw [←(Fintype.equivFin I).symm.prod_comp (fun i=>series (e i) (he i))]
  rw [series_fin_pi]
  exact series_equiv _ _ (finitePiReindex A) (finitePiReindex_energy A e)
end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
