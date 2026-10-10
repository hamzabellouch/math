import Mathlib
import OAI.Geometry.Borsuk.Support.SixFaces

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
attribute [local instance] Classical.propDecidable
section Within
variable {α : Type*} [DecidableEq α]
noncomputable def withinLabels (C U : Finset α) : Finset C := U.subtype (· ∈ C)
@[simp] lemma mem_withinLabels {C U : Finset α} {i : C} :
    i ∈ withinLabels C U ↔ i.val ∈ U := Finset.mem_subtype
lemma withinLabels_card {C U : Finset α} (hUC : U ⊆ C) : (withinLabels C U).card = U.card := by
  rw [withinLabels,Finset.card_subtype,Finset.filter_true_of_mem]
  exact fun _ hi => hUC hi
lemma withinLabels_compl (C U : Finset α) :
    withinLabels C (C \ U) = (withinLabels C U)ᶜ := by
  ext i
  simp [i.property]
lemma withinLabels_insert (C U : Finset α) (i : C) :
    withinLabels C (insert i.val U) = insert i (withinLabels C U) := by
  ext j
  simp only [mem_withinLabels,Finset.mem_insert,Subtype.ext_iff]
end Within

section FacetSix
variable {f : Vector4 → Fin 10 → ℝ}

lemma Admissible.facet_complement_exclusion (hf : Admissible f) {S U : Finset (Fin 10)}
    (hS : SupportFace f S) (hU : SupportFace f U) : ¬ SupportFace f (Sᶜ \ U) := by
  classical
  rintro ⟨v,hv,hCv⟩
  obtain ⟨w,hw,hSw⟩ := hS
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 3) (by decide) ![w,u,v] (by
    intro j
    fin_cases j <;> simp [hw,hu,hv])
  by_cases hiS : i ∈ S
  · exact hi 0 (hSw hiS)
  by_cases hiU : i ∈ U
  · exact hi 1 (hUu hiU)
  exact hi 2 (hCv (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hiS,hiU⟩))

lemma restricted_face_image {C U : Finset (Fin 10)} (hUC : U ⊆ C)
    (e : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] Vector4)
    (hU : SupportFace (fun x (i : C) => f (e x) i.val) (withinLabels C U)) :
    SupportFace f U := by
  obtain ⟨x,hx,hUx⟩ := hU
  refine ⟨e x,by simpa using hx,?_⟩
  intro i hi
  exact (mem_positiveSupport _ _ _).mpr ((mem_positiveSupport _ _ (⟨i,hUC hi⟩ : C)).mp
    (hUx (mem_withinLabels.mpr hi)))

lemma Admissible.facet_six_properties (hf : Admissible f) {S : Finset (Fin 10)}
    (hSc : S.card = 4) (hSf : SupportFace f S) :
    (∀ U ⊆ Sᶜ, U.card = 3 → (SupportFace f U ↔ ¬ SupportFace f (Sᶜ \ U))) ∧
    (∀ P ⊆ Sᶜ, P.card = 2 →
      ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card = 2) := by
  classical
  obtain ⟨w,hw,hSw⟩ := hSf
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hw
  let C : Finset (Fin 10) := Sᶜ
  let g : EuclideanSpace ℝ (Fin 3) → C → ℝ := fun x i => f (e x) i.val
  have hCc : C.card = 6 := by dsimp [C]; rw [Finset.card_compl,Fintype.card_fin,hSc]
  have hcard : Fintype.card C = 6 := by simpa using hCc
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ C, f (e x) i = 0 := by
    intro x hx i hi
    have hiS : i ∈ S := by simpa [C] using hi
    have hwpos : 0 < f w i := (mem_positiveSupport _ _ _).mp (hSw hiS)
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal w (e x) hw
      (by simpa using hx) (he x) i ⟨hwpos,hp⟩)) (hf.nonneg _ (by simpa using hx) i)
  have hg : Admissible g := (hf.comp_isometry e).restrict_labels C hzero
  have hmap {U : Finset (Fin 10)} (hUC : U ⊆ C) :
      SupportFace g (withinLabels C U) → SupportFace f U := restricted_face_image hUC e
  have hfaces {U : Finset (Fin 10)} (hUC : U ⊆ C) (hUc : U.card = 3) :
      SupportFace g (withinLabels C U) ↔ SupportFace f U := by
    refine ⟨hmap hUC,?_⟩
    intro hU
    apply (hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])).mpr
    rw [← withinLabels_compl]
    intro hcomp
    exact hf.facet_complement_exclusion ⟨w,hw,hSw⟩ hU (hmap Finset.sdiff_subset hcomp)
  constructor
  · intro U hUC hUc
    have hcUc : (C \ U).card = 3 := by rw [Finset.card_sdiff_of_subset hUC,hCc,hUc]
    rw [← hfaces hUC hUc,← hfaces Finset.sdiff_subset hcUc,withinLabels_compl]
    exact hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])
  · intro P hPC hPc
    let P' := withinLabels C P
    have hP'c : P'.card = 2 := by rw [withinLabels_card hPC,hPc]
    have hinsert {i : C} (hi : i ∉ P') :
        SupportFace g (insert i P') ↔ SupportFace f (insert i.val P) := by
      have hiP : i.val ∉ P := by simpa only [P',mem_withinLabels] using hi
      have hh := hfaces (Finset.insert_subset i.property hPC)
        (by rw [Finset.card_insert_of_notMem hiP,hPc])
      simpa only [withinLabels_insert] using hh
    have hc := hg.six_pair_count hcard hP'c
    have hcount : ((P'ᶜ).filter (fun i => SupportFace g (insert i P'))).card =
        ((C \ P).filter (fun i => SupportFace f (insert i P))).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        obtain ⟨hiP,hif⟩ := Finset.mem_filter.mp hi
        have hiP' := Finset.mem_compl.mp hiP
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨i.property,by
          simpa only [P',mem_withinLabels] using hiP'⟩,(hinsert hiP').mp hif⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        obtain ⟨hiC,hif⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiC,hiP⟩ := Finset.mem_sdiff.mp hiC
        have hiP' : (⟨i,hiC⟩ : C) ∉ P' := by simpa only [P',mem_withinLabels] using hiP
        exact ⟨⟨i,hiC⟩,Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hiP',(hinsert hiP').mpr hif⟩,rfl⟩
    exact hcount.symm.trans hc
end FacetSix
end BorsukNine

end OAI
