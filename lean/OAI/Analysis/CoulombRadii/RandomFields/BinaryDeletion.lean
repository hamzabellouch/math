import Mathlib
import OAI.Analysis.CoulombRadii.Localization.TotalDeletion
import OAI.Analysis.CoulombRadii.FieldAnalysis.ColoredObservable

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma coloredDeletion_reindex {J m k n : ℕ} (S : Nuclei J) (h t : ℝ)
    (p : Fin n → Fin 2) (e : Fin (m+k) ≃ Fin n)
    (he0 : ∀ i, p (e (Fin.castAdd k i))=0) (he1 : ∀ i, p (e (Fin.natAdd m i))=1)
    (x : Configuration (m+k)) :
    coloredObservable (particleInnerExterior S h t) p (reindexConfiguration e x)=
      outerDeletionField (m:=m) (k:=k) S h t x := by
  unfold coloredObservable
  rw [←Equiv.sum_comp e (fun i : Fin n => if p i=0 then particleInnerExterior S h t i (reindexConfiguration e x) else 0)]
  simp only [particleInnerExterior_reindex,Fin.sum_univ_add,he0,he1,ite_true,
    show (1:Fin 2)≠0 by decide,ite_false,Finset.sum_const_zero,add_zero,outerDeletionField]

lemma coloredDeletion_labelCut {J n : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    (u : H1Vector n) (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    {h t : ℝ} (ht : 0<t) (hh : h≤t/2) (hinner : ∀ y, ‖y‖<t → χ 0 y=0) :
    (∑ p : Fin n → Fin 2, potentialForm (coloredObservable (particleInnerExterior S h t) p)
      (u.labelCut χ hχ hp D hD hd p))=
      potentialForm (weightedInnerField S h (fun y => χ 0 y^2)) u := by
  rw [potentialForm_colored_labelCut u χ hχ hp D hD hd _
    (particleInnerExterior_measurable S h t) (show 0≤totalCharge S/t+(n:ℝ)/(t/2) by
      exact add_nonneg (div_nonneg (totalCharge_nonneg S) ht.le) (by positivity))
    (particleInnerExterior_abs_le S hatom ht hh)]
  congr 1
  funext x
  unfold weightedInnerField
  apply Finset.sum_congr rfl
  intro i hi
  unfold particleInnerExterior
  split_ifs with hy
  · rfl
  · simp [hinner _ (lt_of_not_ge hy)]

namespace RecordedEnsemble

def totalCoreForm {J n : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x => form S ((T.vector p).coreSlice s x).normalized)

theorem binary_localization_deletion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    {h t : ℝ} (ht : 0<t) (hh : h≤t/2) (hinner : ∀ y, ‖y‖<t → χ 0 y=0)
    (B : Set Space) (hB : ∀ y∉B, χ 1 y=0) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported B ∧
      T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=mass ψ ∧
      T.totalForm S=∑ p : Fin n → Fin 2, form S (ψ.labelCut χ hχ hp D hD hd p) ∧
      T.totalCoreForm S ≤ T.totalForm S+potentialForm (weightedInnerField S h (fun y => χ 0 y^2)) ψ := by
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
  have hanti (p : Fin n → Fin 2) : PartlyAntisymmetric (v p) (coreIndexSet (m p) (k p)) := by
    let K : Set (Fin n) := {i | p i=1}
    have hc := (hψ.partly (Set.univ : Set (Fin n))).labelCut χ hχ hp D hD hd p K
      (Set.subset_univ _) 1 (fun _ h => h)
    exact hc.reindex (e p) (coreIndexSet (m p) (k p)) (by rintro _ ⟨i,rfl⟩; exact he1 p i)
  have hsupp (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) (C : Set Space) (hC : ∀ y∉C, χ l y=0) :
      PartlySupported (v p) I C := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := labelCut_partlySupported ψ χ hχ hp D hD hd p K l (fun _ h => h) C hC
    exact hc.reindex (e p) I hi
  have hout p : PartlySupported (v p) (outIndexSet (m p) (k p)) {y | t≤‖y‖} :=
    hsupp p _ 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i) _ (fun y hy => hinner y (lt_of_not_ge hy))
  refine ⟨T,?_,hanti,?_,hout,?_,?_,?_⟩
  · intro W hW hbound
    dsimp [T,v]
    simp only [potentialForm_reindex]
    obtain ⟨M,hM⟩ := hbound
    exact potentialForm_labelCut ψ χ hχ hp D hD hd W hW hM
  · intro p
    exact hsupp p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i) B hB
  · dsimp [totalMass,T,v]
    simp only [mass_reindex]
    exact mass_labelCut ψ χ hχ hp D hD hd
  · dsimp [totalForm,T,v]
    simp only [form_reindex]
  · have hc p := slice_core_form_le_raw_deletion S hatom (v p) ht hh (hout p)
    have he p : potentialForm (outerDeletionField (m:=m p) (k:=k p) S h t) (v p)=
        potentialForm (coloredObservable (particleInnerExterior S h t) p)
          (ψ.labelCut χ hχ hp D hD hd p) := by
      have hf : outerDeletionField (m:=m p) (k:=k p) S h t=
          coloredObservable (particleInnerExterior S h t) p ∘ reindexConfiguration (e p) := by
        funext x
        exact (coloredDeletion_reindex S h t p (e p) (he0 p) (he1 p) x).symm
      rw [hf]
      exact potentialForm_reindex _ _ _
    have hu := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => hc p)
    simp only [Finset.sum_add_distrib,he,coloredDeletion_labelCut S hatom ψ χ hχ hp D hD hd ht hh hinner] at hu
    exact hu

end RecordedEnsemble
end Coulomb
end

end

end OAI
