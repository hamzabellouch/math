import Mathlib
import OAI.Geometry.Borsuk.Support.AllPairs

namespace OAI

open Set MeasureTheory
namespace BorsukNine
attribute [local instance] Classical.propDecidable
open scoped RealInnerProductSpace
section SixFaces
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)
lemma Admissible.six_complement_exclusion {f : E → ι → ℝ} (hf : Admissible f)
    {U : Finset ι} (hU : SupportFace f U) : ¬ SupportFace f Uᶜ := by
  classical
  rintro ⟨v,hv,hUv⟩
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 2) (by decide) ![u,v] (by
    intro j
    fin_cases j <;> simp [hu,hv])
  by_cases h : i ∈ U
  · exact hi 0 (hUu h)
  · exact hi 1 (hUv (Finset.mem_compl.mpr h))

lemma Admissible.six_pair_lower {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
  classical
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hPc
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hui,huj⟩ := hf.all_pairs hdim hij
  have hpair : SupportFace f {i,j} := ⟨u,hu,by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact (mem_positiveSupport _ _ _).mpr hui
    · exact (mem_positiveSupport _ _ _).mpr huj⟩
  obtain ⟨I,hIc,hIf,hPI⟩ := hf.face_extends_three hcard hpair
  obtain ⟨I',hI'c,hI'f,hPI',hne⟩ := hf.triangle_no_free_edge hcard hIc hIf hPI (by simp [hij])
  have hsub : {I,I'} ⊆ (SixCounting.triangles Finset.univ (SupportFace f)).filter ({i,j} ⊆ ·) := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hIc,hIf⟩,hPI⟩
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hI'c,hI'f⟩,hPI'⟩
  have hc := Finset.card_le_card hsub
  simpa [hne.symm] using hc

lemma Admissible.six_complementary {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hUc : U.card = 3) :
    SupportFace f U ↔ ¬ SupportFace f Uᶜ := by
  classical
  have hC : (Finset.univ : Finset ι).card = 6 := by simpa using hcard
  have hd : ∀ U ∈ (Finset.univ : Finset ι).powersetCard 3,
      SupportFace f U → ¬ SupportFace f (Finset.univ \ U) := by
    intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  have hp : ∀ P ∈ (Finset.univ : Finset ι).powersetCard 2,
      2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
    intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
  simpa only [← Finset.compl_eq_univ_sdiff] using SixCounting.complementary_iff hC hd hp
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U,hUc⟩)

lemma Admissible.six_pair_degree {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card = 2 := by
  classical
  apply SixCounting.pair_degree_eq_two
    (C := Finset.univ) (by simpa using hcard) ?_ ?_ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hPc⟩)
  · intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  · intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
end SixFaces

lemma pair_triangle_card {α : Type*} [DecidableEq α] (C P : Finset α) (T : Finset α → Prop)
    (hPC : P ⊆ C) (hPc : P.card = 2) :
    (SixCounting.triangles C T |>.filter (P ⊆ ·)).card =
      ((C \ P).filter (fun w => T (insert w P))).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => insert w P)
  · intro w hw
    obtain ⟨hw,hT⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwC,hwP⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr
      ⟨Finset.insert_subset hwC hPC,by rw [Finset.card_insert_of_notMem hwP,hPc],hT⟩,Finset.subset_insert _ _⟩
  · intro w hw v hv he
    have hwP := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    have hm : w ∈ insert v P := he ▸ Finset.mem_insert_self w P
    exact (Finset.mem_insert.mp hm).resolve_right hwP
  · intro U hU
    obtain ⟨hU,hPU⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUC,hUc,hT⟩ := SixCounting.mem_triangles.mp hU
    have hd : (U \ P).card = 1 := by rw [Finset.card_sdiff_of_subset hPU,hUc,hPc]
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hd
    have hwm : w ∈ U \ P := by rw [hw]; simp
    obtain ⟨hwU,hwP⟩ := Finset.mem_sdiff.mp hwm
    have he : insert w P = U := by
      have hh := Finset.sdiff_union_of_subset hPU
      simpa only [hw,Finset.singleton_union] using hh
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hUC hwU,hwP⟩,he ▸ hT⟩,he⟩

lemma Admissible.six_pair_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace ℝ (Fin 3) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((Pᶜ : Finset ι).filter (fun w => SupportFace f (insert w P))).card = 2 := by
  classical
  rw [Finset.compl_eq_univ_sdiff,← pair_triangle_card _ _ _ (Finset.subset_univ P) hPc]
  exact hf.six_pair_degree hcard hPc
end BorsukNine

end OAI
