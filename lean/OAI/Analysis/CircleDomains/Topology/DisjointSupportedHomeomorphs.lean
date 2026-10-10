import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-! Finite composition of smooth plane deformations supported in disjoint
open neighborhoods preserves the exact image assigned to each cap. -/
open Set Function
open scoped ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_maps_set_of_fixed_compl (T : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hfix : ∀z∉U,T z=z) {x : ℂ} (hx : x∈U) : T x∈U := by
  by_contra hn
  have he : T x=x := T.injective (hfix _ hn)
  rw [he] at hn
  exact hn hx

lemma exists_disjoint_supported_composition {I : Type*} [Fintype I]
    (A U : I → Set ℂ) (hA : ∀i,A i⊆U i)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (T : I → ℂ ≃ₜ ℂ) (hs : ∀i,ContDiff ℝ ∞ (T i : ℂ → ℂ))
    (hsi : ∀i,ContDiff ℝ ∞ ((T i).symm : ℂ → ℂ))
    (hfix : ∀i z,z∉U i → T i z=z) :
    ∃P : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (P : ℂ → ℂ) ∧
      ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀z,(∀i,z∉U i) → P z=z) ∧ ∀i,P '' A i=T i '' A i := by
  classical
  have hfixed (i j : I) (hij : i≠j) {B : Set ℂ} (hB : B⊆U j) : T i '' B=B := by
    calc
      T i '' B = id '' B := image_congr (fun z hz => hfix i z
        (fun hi => Set.disjoint_left.mp (hU hij) hi (hB hz)))
      _ = B := image_id B
  have hfamily (s : Finset I) :
      ∃P : ℂ ≃ₜ ℂ,ContDiff ℝ ∞ (P : ℂ → ℂ) ∧
        ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
        (∀z,(∀i,z∉U i) → P z=z) ∧ ∀i,P '' A i=if i∈s then T i '' A i else A i := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Homeomorph.refl ℂ,contDiff_id,contDiff_id,fun _ _ => rfl,?_⟩
      intro i
      simp
    | @insert i s hi ih =>
      obtain ⟨P,hPs,hPis,hPf,hP⟩ := ih
      refine ⟨P.trans (T i),(hs i).comp hPs,hPis.comp (hsi i),?_,?_⟩
      · intro z hz
        change T i (P z)=z
        rw [hPf z hz,hfix i z (hz i)]
      intro j
      change (T i ∘ P) '' A j=_
      rw [image_comp,hP]
      by_cases hji : j=i
      · subst j
        simp [hi]
      · by_cases hjs : j∈s
        · simp only [ite_eq_left hjs,Finset.mem_insert,hji,false_or]
          exact hfixed i j (Ne.symm hji) (by
            rintro _ ⟨x,hx,rfl⟩
            exact homeomorph_maps_set_of_fixed_compl (T j) (hfix j) (hA j hx))
        · simp only [ite_eq_right hjs,Finset.mem_insert,hji,false_or]
          exact hfixed i j (Ne.symm hji) (hA j)
  obtain ⟨P,hPs,hPis,hPf,hP⟩ := hfamily Finset.univ
  refine ⟨P,hPs,hPis,hPf,?_⟩
  intro i
  simpa only [Finset.mem_univ,ite_eq_left] using hP i

end CircleDomainRigidity

end

end OAI
