import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.SortedCut
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawObservable
import OAI.Analysis.CoulombRadii.Screening.CountMoments

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def reindexConfiguration {m n : ℕ} (e : Fin m ≃ Fin n) (x : Configuration m) : Configuration n :=
  WithLp.toLp 2 (fun ib => x (e.symm ib.1,ib.2))

lemma restrictedOutPotential_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (x : Configuration m) (A : Set Space) (y : Space) :
    restrictedOutPotential (reindexConfiguration e x) A y=restrictedOutPotential x A y := by
  change (∑ i : Fin n, if position x (e.symm i) ∈ A then coulombKernel (position x (e.symm i)-y) else 0)=_
  exact Equiv.sum_comp e.symm (fun i => if position x i ∈ A then coulombKernel (position x i-y) else 0)

lemma rawSignedField_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (V : ℝ) (A : Set Space) (y : Space) (x : Configuration m) :
    rawSignedField V A y (reindexConfiguration e x)=rawSignedField V A y x := by
  simp only [rawSignedField,restrictedOutPotential_reindex]

lemma labelCut_outer_support {m k : ℕ} {L : Type*} [Fintype L]
    (ψ : H1Vector (m+k))
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+k) → L) (l : L) (hc : ∀ i, p (Fin.castAdd k i)=l)
    (A : Set Space) (hA : ∀ z ∉ A, χ l z=0) (s : Spins m) :
    ∀ᵐ x, mass ((ψ.labelCut χ hχ hp D hD hd p).coreSlice s x) ≠0 →
      ∀ i, position x i ∈ A := by
  let u := ψ.labelCut χ hχ hp D hD hd p
  filter_upwards [u.coreSliceRegular_ae s] with x hx hm i
  by_contra hi
  have hv (t : Spins k) (v : Configuration k) : (u.coreSlice s x).value t v=0 := by
    rw [u.coreSlice_value s hx]
    change (↑(tensorCut χ p (joinConfiguration m k (x,v))):ℂ)*ψ.value (Fin.append s t)
      (joinConfiguration m k (x,v))=0
    have H : tensorCut χ p (joinConfiguration m k (x,v))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (Fin.castAdd k i))
      rw [hc,position_join_left,hA _ hi]
    rw [H,Complex.ofReal_zero,zero_mul]
  apply hm
  change mass (u.coreSlice s x)=0
  simp only [mass,hv,norm_zero,zero_pow (by decide : 2≠0),integral_zero,Finset.sum_const_zero]

lemma outLabelCount_order {m k n : ℕ} (p : Fin n → Fin 2) (e : Fin (m+k) ≃ Fin n)
    (h0 : ∀ i : Fin m, p (e (Fin.castAdd k i))=0)
    (h1 : ∀ i : Fin k, p (e (Fin.natAdd m i))=1) : outLabelCount p=(m:ℝ) := by
  unfold outLabelCount
  rw [← Equiv.sum_comp e (fun i => if p i=0 then (1:ℝ) else 0),Fin.sum_univ_add]
  simp [h0,h1]

theorem binary_cut_recorded_outcome {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → Fin 2) (A B : Set Space)
    (hA : ∀ z ∉ A, χ 1 z=0) (hB : ∀ z ∉ B, χ 0 z=0) :
    ∃ m k : ℕ, ∃ u : H1Vector (m+k), ∃ e : Fin (m+k) ≃ Fin n,
      m+k=n ∧ outLabelCount p=(m:ℝ) ∧
      mass u=mass (ψ.labelCut χ hχ hp D hD hd p) ∧
      form S u=form S (ψ.labelCut χ hχ hp D hD hd p) ∧
      (∀ W : Configuration n → ℝ,
        (∀ q x, W (permute q x)=W x) →
        potentialForm (fun x => W (reindexConfiguration e x)) u=potentialForm W (ψ.labelCut χ hχ hp D hD hd p)) ∧
      (∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x)) ∧
      (∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x) A) ∧
      (∀ s, ∀ᵐ x, mass (u.coreSlice s x) ≠0 → ∀ i, position x i ∈ B) := by
  obtain ⟨m,k,e,he0,he1⟩ := exists_binary_order p
  have hn : m+k=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  let v := ψ.labelCut χ hχ hp D hD hd p
  let u := (ψ.permutation e.symm).labelCut χ hχ hp D hD hd (p ∘ e)
  have hval (s : Spins (m+k)) : (v.permutation e.symm).value s =ᵐ[volume] u.value s := by
    exact Eventually.of_forall (fun x => labelCut_permute_value ψ χ hχ hp D hD hd p e.symm s x)
  refine ⟨m,k,u,e,rfl,outLabelCount_order p e he0 he1,?_,?_,?_,?_,?_,?_⟩
  · rw [← mass_congr_ae _ _ hval,mass_permutation]
  · rw [← form_congr_ae S _ _ hval,form_permutation]
  · intro W hW
    have hw : (fun x => W (reindexConfiguration e x))=W := by
      funext x
      exact hW e.symm x
    rw [hw]
    change potentialEnergy W u=potentialEnergy W v
    rw [← potentialEnergy_congr_ae _ _ _ hval,potentialEnergy_permutation W hW]
  · intro s
    exact labelCut_core_antisymmetric _ (hψ.permutation e.symm) χ hχ hp D hD hd (p ∘ e) 1 he1 s
  · intro s
    exact labelCut_core_support _ χ hχ hp D hD hd (p ∘ e) 1 he1 A hA s
  · intro s
    exact labelCut_outer_support _ χ hχ hp D hD hd (p ∘ e) 0 he0 B hB s

end Coulomb
end

end
end

end OAI
