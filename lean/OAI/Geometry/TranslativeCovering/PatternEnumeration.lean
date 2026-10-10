import OAI.Geometry.TranslativeCovering.WeightedVolume

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PatternEnumeration
open Set Metric MeasureTheory PatternGeometry LocalizationRounding
open scoped BigOperators ENNReal Classical
lemma good_reindex {n : ℕ} {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → PatternGeometry.Space n) (a D r L C : ℝ) :
    roundedGood (p ∘ e) a D r L C = roundedGood p a D r L C := by
  ext y
  have hc : (relevant (p ∘ e) L y).card = (relevant p L y).card := by
    simp only [relevant,Finset.card_filter,Function.comp_apply]
    exact e.sum_comp (fun j => if ‖y-p j‖ ≤ L then 1 else 0)
  have hs : (∑ i ∈ relevant (p ∘ e) L y,weight n a ‖y-(p ∘ e) i‖) =
      ∑ j ∈ relevant p L y,weight n a ‖y-p j‖ := by
    simp only [relevant,Finset.sum_filter,Function.comp_apply]
    exact e.sum_comp (fun j => if ‖y-p j‖ ≤ L then weight n a ‖y-p j‖ else 0)
  have hall : (∀ i : I,r ≤ ‖y-(p ∘ e) i‖) ↔ (∀ j : J,r ≤ ‖y-p j‖) := by
    constructor
    · intro hh j
      obtain ⟨i,rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  simp only [roundedGood,mem_ofPred_eq,hc,hs,hall]

noncomputable def points {n N : ℕ} {h L : ℝ} (P : BoundedLists n h L N) : Fin P.1.val → PatternGeometry.Space n :=
  fun i => (P.2 i).val

lemma encode {n N : ℕ} {h L : ℝ} {J : Type u_3} [Fintype J]
    (p : J → PatternGeometry.Space n) (hcard : Fintype.card J ≤ N) (hp : ∀ j,p j ∈ alphabet n h L) :
    ∃ P : BoundedLists n h L N,∃ e : Fin P.1.val ≃ J,points P = p ∘ e := by
  let P : BoundedLists n h L N := ⟨⟨Fintype.card J,by omega⟩,
    fun i => ⟨p ((Fintype.equivFin J).symm i),hp _⟩⟩
  exact ⟨P,(Fintype.equivFin J).symm,rfl⟩

abbrev Retained (n N : ℕ) (h L a D r b C : ℝ) :=
  {P : BoundedLists n h L N // volume (closedBall (0 : PatternGeometry.Space n) D) ≤
    4*volume (roundedGood (points P) a D r b C)}

noncomputable instance retainedFintype (n N : ℕ) (h L a D r b C : ℝ) :
    Fintype (Retained n N h L a D r b C) := Fintype.ofFinite _

lemma retained_card (n N : ℕ) (h L a D r b C : ℝ) :
    Fintype.card (Retained n N h L a D r b C) ≤
      (N+1)*max 1 (alphabet n h L).card^N :=
  (Fintype.card_subtype_le _).trans (boundedLists_card n N h L)

lemma encode_retained {n N : ℕ} {h L a D r b C : ℝ} {J : Type u_4} [Fintype J]
    (p : J → PatternGeometry.Space n) (hcard : Fintype.card J ≤ N) (hp : ∀ j,p j ∈ alphabet n h L)
    (hg : volume (closedBall (0 : PatternGeometry.Space n) D) ≤ 4*volume (roundedGood p a D r b C)) :
    ∃ P : Retained n N h L a D r b C,∃ e : Fin P.val.1.val ≃ J,points P.val = p ∘ e := by
  obtain ⟨P,e,he⟩ := encode p hcard hp
  refine ⟨⟨P,?_⟩,e,he⟩
  rw [he,good_reindex]
  exact hg
end PatternEnumeration

end OAI
