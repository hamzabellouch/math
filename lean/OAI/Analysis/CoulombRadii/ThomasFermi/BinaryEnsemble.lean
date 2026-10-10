import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff
noncomputable section
namespace Coulomb

namespace RecordedEnsemble

def OutFermionic {n : ℕ} (T : RecordedEnsemble n) : Prop :=
  ∀ p, PartlyAntisymmetric (T.vector p) (outIndexSet (T.out p) (T.core p))
def CoreSupported {n : ℕ} (T : RecordedEnsemble n) (A : Set Space) : Prop :=
  ∀ p, PartlySupported (T.vector p) (coreIndexSet (T.out p) (T.core p)) A

theorem binary_localization {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)|≤D)
    (A B : Set Space) (hA : ∀ z∉A, χ 0 z=0) (hB : ∀ z∉B, χ 1 z=0) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported B ∧ T.OutSupported A ∧ T.totalMass=mass ψ ∧
      T.totalForm S=∑ p : Fin n → Fin 2, form S (ψ.labelCut χ hχ hp D hD hd p) := by
  have H (p : Fin n → Fin 2) := exists_binary_order p
  choose m k e he0 he1 using H
  let v (p : Fin n → Fin 2) := (ψ.labelCut χ hχ hp D hD hd p).reindex (e p)
  let T : RecordedEnsemble n := {
    index := Fin n → Fin 2
    finite := inferInstance
    out := m
    core := k
    vector := v
    labels := e }
  have hanti (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) : PartlyAntisymmetric (v p) I := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := (hψ.partly (Set.univ : Set (Fin n))).labelCut χ hχ hp D hD hd p K
      (Set.subset_univ _) l (fun _ h => h)
    exact hc.reindex (e p) I hi
  have hsupp (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) (C : Set Space) (hC : ∀ z∉C, χ l z=0) :
      PartlySupported (v p) I C := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := labelCut_partlySupported ψ χ hχ hp D hD hd p K l (fun _ h => h) C hC
    exact hc.reindex (e p) I hi
  refine ⟨T,?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW hbound
    dsimp [T,v]
    simp only [potentialForm_reindex]
    obtain ⟨M,hM⟩ := hbound
    exact potentialForm_labelCut ψ χ hχ hp D hD hd W hW hM
  · intro p
    exact hanti p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i)
  · intro p
    exact hanti p (outIndexSet (m p) (k p)) 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i)
  · intro p
    exact hsupp p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i) B hB
  · intro p
    exact hsupp p (outIndexSet (m p) (k p)) 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i) A hA
  · dsimp [totalMass,T,v]
    simp only [mass_reindex]
    exact mass_labelCut ψ χ hχ hp D hD hd
  · dsimp [totalForm,T,v]
    simp only [form_reindex]

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
