import OAI.Geometry.TranslativeCovering.PoissonMeasureCells

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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PoissonDiagrams
open Set MeasureTheory CellMatching PoissonMeasureCells
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} {C : Type u_4} [MeasurableSpace Ω] [Fintype I] [Fintype J] [Fintype C]

omit [Fintype C] in

def classSet (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω) : Classes M → Set Ω :=
  Sum.elim (fun i => {x | x ∈ E i ∧ ∀ j, (i,j) ∈ M.val → x ∈ F j}) (fun j => F j.val)

omit [Fintype C] [MeasurableSpace Ω] in
lemma classSet_left_matched (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    {i : I} {j : J} (hij : (i,j) ∈ M.val) :
    classSet M E F (Sum.inl i) = E i ∩ F j := by
  ext x
  constructor
  · intro h
    exact ⟨h.1,h.2 j hij⟩
  · rintro ⟨hE,hF⟩
    refine ⟨hE, ?_⟩
    intro k hik
    rwa [M.property.1 _ _ _ hik hij]

omit [Fintype C] [MeasurableSpace Ω] in
lemma classSet_left_unmatched (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    {i : I} (hi : ∀ j, (i,j) ∉ M.val) : classSet M E F (Sum.inl i) = E i := by
  ext x
  simp only [classSet, Sum.elim_inl, mem_ofPred_eq, hi, false_implies, implies_true, and_true]

omit [Fintype C] in
lemma classSet_measurable (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ j, MeasurableSet (F j)) :
    ∀ v, MeasurableSet (classSet M E F v) := by
  rintro (i | j)
  · by_cases hi : ∃ j, (i,j) ∈ M.val
    · rw [classSet_left_matched M E F hi.choose_spec]
      exact (hE i).inter (hF hi.choose)
    · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]
      exact hE i
  · exact hF j

lemma classSet_respects (P : Partition Ω C) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (hE : ∀ i, Respects P (E i))
    (hF : ∀ j, Respects P (F j)) : ∀ v, Respects P (classSet M E F v) := by
  rintro (i | j)
  · by_cases hi : ∃ j, (i,j) ∈ M.val
    · rw [classSet_left_matched M E F hi.choose_spec]
      exact respects_inter P (hE i) (hF hi.choose)
    · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]
      exact hE i
  · exact hF j

lemma classSet_incidence (P : Partition Ω C) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (v : Classes M) (c : C) :
    P.cell c ⊆ classSet M E F v ↔
      classIncidence M (fun i c => P.cell c ⊆ E i) (fun j c => P.cell c ⊆ F j) v c := by
  rcases v with i | j
  · constructor
    · intro h
      refine ⟨fun x hx => (h hx).1, ?_⟩
      intro j hij x hx
      exact (h hx).2 j hij
    · rintro ⟨hE,hF⟩ x hx
      exact ⟨hE hx,fun j hij => hF j hij hx⟩
  · rfl

omit [Fintype C] in
lemma classSet_mass_left (μ : Measure Ω) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (i : I) :
    μ.real (classSet M E F (Sum.inl i)) =
      MatchingAlgebra.leftWeight M.val (fun i => μ.real (E i))
        (fun i j => μ.real (E i ∩ F j)) i := by
  unfold MatchingAlgebra.leftWeight
  split_ifs with hi
  · rw [classSet_left_matched M E F hi.choose_spec]
  · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]

omit [Fintype C] in

noncomputable def diagram (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) : ℝ :=
  (∏ i, μ.real (E i)) * (∏ j, μ.real (F j)) *
    ∑ M : Matching I J, if M.val.Nonempty then
      ∏ ij ∈ M.val, μ.real (E ij.1 ∩ F ij.2) / (μ.real (E ij.1) * μ.real (F ij.2))
      else 0

omit [Fintype C] in
lemma classSet_product (μ : Measure Ω) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, μ.real (E i) ≠ 0) (hF : ∀ j, μ.real (F j) ≠ 0) :
    (∏ v, μ.real (classSet M E F v)) =
      (∏ i, μ.real (E i)) * (∏ j, μ.real (F j)) *
        ∏ ij ∈ M.val, μ.real (E ij.1 ∩ F ij.2) / (μ.real (E ij.1) * μ.real (F ij.2)) := by
  rw [Fintype.prod_sum_type]
  simp_rw [classSet_mass_left]
  exact MatchingAlgebra.normalized_diagram_identity M.val M.property.1 M.property.2
    _ _ _ hE hF

omit [Fintype C] in
lemma diagram_eq_classSet_sum (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, μ.real (E i) ≠ 0) (hF : ∀ j, μ.real (F j) ≠ 0) :
    diagram μ E F = ∑ M : Matching I J, if M.val.Nonempty then
      ∏ v, μ.real (classSet M E F v) else 0 := by
  rw [diagram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hm : M.val.Nonempty
  · rw [ite_eq_left hm, ite_eq_left hm, classSet_product μ M E F hE hF]
  · rw [ite_eq_right hm, ite_eq_right hm, mul_zero]

lemma dependency_eq_sum_Q (μ : Measure Ω) (P : Partition Ω C)
    (E : I → Set Ω) (F : J → Set Ω) :
    (∑ fg : (I ↪ C) × (J ↪ C), if (support fg.1 ∩ support fg.2).Nonempty then
      pairWeight (fun i c => P.cell c ⊆ E i) (fun j c => P.cell c ⊆ F j)
        (fun c => 1 - Real.exp (-μ.real (P.cell c))) fg else 0) =
      ∑ M : Matching I J, if M.val.Nonempty then Q μ P (classSet M E F) else 0 := by
  rw [dependency_diagram_sum]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hm : M.val.Nonempty
  · rw [ite_eq_left hm, ite_eq_left hm, Q, CellCounts.injectiveSum_slot_eq]
    simp_rw [classSet_incidence]
  · rw [ite_eq_right hm, ite_eq_right hm]

omit [Fintype C] [Fintype J] in

lemma Q_tendsto {T : Type u_5} {l : Filter T} (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : T → Type u_6) [∀ t, Fintype (C t)] (P : ∀ t, Partition Ω (C t))
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hr : ∀ t i, Respects (P t) (E i)) {δ : T → ℝ}
    (hδ : ∀ t, 0 ≤ δ t) (hd : ∀ t c, μ.real ((P t).cell c) ≤ δ t)
    (hlim : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto (fun t => Q μ (P t) E) l (nhds (∏ i, μ.real (E i))) := by
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let B : ℝ := (Fintype.card I : ℝ)/2 * (∏ i, μ.real (E i)) +
        ∑ ij ∈ CellCounts.pairs I, μ.real (E ij.1 ∩ E ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, μ.real (E u)
  have hbound (t : T) := collision_error μ (P t) E hE (hr t) (hδ t) (hd t)
  have herr : Filter.Tendsto (fun t => (∏ i, μ.real (E i)) - Q μ (P t) E) l (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (hbound t).1))
      (Filter.Eventually.of_forall (fun t => (hbound t).2))
    simpa only [zero_mul] using hlim.mul_const B
  have ht := (tendsto_const_nhds (x := ∏ i, μ.real (E i))).sub herr
  simpa only [sub_sub_cancel, sub_zero] using ht

omit [MeasurableSpace Ω] [Fintype J] [Fintype C] in
noncomputable def identityMatching (I : Type u_7) [Fintype I] : Matching I I :=
  ⟨Finset.univ.diag, by
    constructor
    · intro i j k hij hik
      simp only [Finset.mem_diag] at hij hik
      exact hij.2.symm.trans hik.2
    · intro i j k hik hjk
      simp only [Finset.mem_diag] at hik hjk
      exact hik.2.trans hjk.2.symm⟩

omit [MeasurableSpace Ω] [Fintype J] [Fintype C] in
@[simp] lemma mem_identityMatching (i j : I) :
    (i,j) ∈ (identityMatching I).val ↔ i = j := by
  simp only [identityMatching, Finset.mem_diag, Finset.mem_univ, true_and]

omit [Fintype J] [Fintype C] in

lemma identity_contribution (μ : Measure Ω) (E : I → Set Ω) :
    (∏ v, μ.real (classSet (identityMatching I) E E v)) = ∏ i, μ.real (E i) := by
  let : IsEmpty {j : I // ∀ i, (i,j) ∉ (identityMatching I).val} :=
    ⟨fun j => j.property j.val ((mem_identityMatching _ _).mpr rfl)⟩
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  apply Finset.prod_congr rfl
  intro i _
  rw [classSet_left_matched _ _ _ ((mem_identityMatching i i).mpr rfl), inter_self]

omit [Fintype J] [Fintype C] in
lemma activity_le_self_diagram (μ : Measure Ω) (E : I → Set Ω)
    [Nonempty I] (hE : ∀ i, μ.real (E i) ≠ 0) :
    (∏ i, μ.real (E i)) ≤ diagram μ E E := by
  rw [diagram_eq_classSet_sum μ E E hE hE]
  have hne : (identityMatching I).val.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨(i,i), (mem_identityMatching i i).mpr rfl⟩
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun M : Matching I I => if M.val.Nonempty then
      ∏ v, μ.real (classSet M E E v) else 0)
    (fun M _ => by split_ifs <;> positivity) (Finset.mem_univ (identityMatching I))
  simpa only [ite_eq_left hne, identity_contribution] using h

end PoissonDiagrams

end OAI
