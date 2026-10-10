import Mathlib
import OAI.Combinatorics.KMedian.Amplification.RegularizationSound

namespace OAI

section Inline_PCPFlexibleCloud

namespace MetricKMedian.PCP
open Finset CloudCopies
open scoped BigOperators Classical

namespace FlexibleCloud
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
variable (embed : ∀ v : Active C, Incident C v ↪ Copy C v)

noncomputable def dartEmbed : Dart (E := E) ↪ Node C where
  toFun d := ⟨owner C d, embed (owner C d) ⟨d,rfl⟩⟩
  inj' := by
    intro d e h
    have ho : owner C d=owner C e := congrArg Sigma.fst h
    have hh : (⟨owner C d,⟨d,rfl⟩⟩ : (v : Active C) × Incident C v) =
        ⟨owner C e,⟨e,rfl⟩⟩ := by
      apply (Function.Embedding.sigmaMap (Function.Embedding.refl _) (embed)).injective
      exact h
    exact congrArg (fun p : (v : Active C) × Incident C v => p.2.val) hh

variable [Fintype A] [DecidableEq A]

noncomputable def matchingGraph : PortGraph (Node C) Unit := dartGraph.extend (dartEmbed C embed)
noncomputable def matchingCSP : PortCSP (matchingGraph C embed) A := (dartCSP C).extend (dartEmbed C embed)

omit [Fintype V] in
@[simp] lemma matching_bad (a : Node C → A) (e : E) :
    (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()) ↔
      (a (dartEmbed C embed (e,false)),a (dartEmbed C embed (e,true))) ∉ C.allowed e := by
  change ((dartCSP C).extend (dartEmbed C embed)).Bad a (dartEmbed C embed (e,false),()) ↔ _
  rw [PortCSP.extend_bad_image (dartCSP C) (dartEmbed C embed) a ((e,false),())]
  simp [PortCSP.Bad,dartCSP,dartGraph,PortGraph.step,dartFlip]

abbrev RegularPort := PortGraph.BlendPort (D := Unit) (S := ExpanderFamily.Degree)
noncomputable def regularGraph : PortGraph (Node C) RegularPort := (matchingGraph C embed).blend (equalityGraph C)
noncomputable def regularCSP : PortCSP (regularGraph C embed) A := (matchingCSP C embed).blend (equalityCSP C)

omit [Fintype V] [Fintype A] [DecidableEq A] in
@[simp] lemma honest_dart (x : V → A) (d : Dart (E := E)) :
    honest C x (dartEmbed C embed d)=x (endpoint C d) := rfl

omit [Fintype V] in
lemma matching_complete (x : V → A) (hx : C.Satisfies x) :
    (matchingCSP C embed).Satisfies (honest C x) := by
  intro n d
  by_cases hn : n ∈ Set.range (dartEmbed C embed)
  · obtain ⟨⟨e,b⟩,rfl⟩ := hn
    change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C embed) (dartEmbed C embed (e,b),d)
    rw [PortCSP.extendedAllowed_image (dartCSP C) (dartEmbed C embed) ((e,b),d)]
    change (honest C x (dartEmbed C embed (e,b)),
      honest C x (((dartGraph (E := E)).extend (dartEmbed C embed)).step (dartEmbed C embed (e,b)) d)) ∈ _
    rw [PortGraph.extend_step_image]
    cases b <;> simpa [dartCSP,dartGraph,PortGraph.step,dartFlip,endpoint] using hx e
  · change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C embed) (n,d)
    rw [PortCSP.extendedAllowed_outside _ _ (n,d) hn]
    exact mem_univ _

omit [Fintype V] in
lemma regular_complete (x : V → A) (hx : C.Satisfies x) :
    (regularCSP C embed).Satisfies (honest C x) :=
  PortCSP.blend_complete _ _ _ (matching_complete C embed x hx) (equality_complete C x)

variable [Inhabited A] [Nonempty E] (a : Node C → A)

omit [Fintype V] [Nonempty E] in
lemma edge_bad_cases (e : E)
    (he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) :
    (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()) ∨
      Disagrees C a (dartEmbed C embed (e,false)) ∨ Disagrees C a (dartEmbed C embed (e,true)) := by
  by_contra h
  simp only [not_or] at h
  have hl : a (dartEmbed C embed (e,false))=decoded C a (C.left e) := by
    exact not_ne_iff.mp h.2.1
  have hr : a (dartEmbed C embed (e,true))=decoded C a (C.right e) := by
    exact not_ne_iff.mp h.2.2
  exact he (by
    have hh := h.1
    rw [matching_bad] at hh
    simpa only [not_not,hl,hr] using hh)

omit [Fintype V] [Nonempty E] in
lemma old_raw :
    testSum (fun e => (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) ≤
      testSum (fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),())) +
        testSum (fun d : Dart (E := E) => Disagrees C a (dartEmbed C embed d)) := by
  unfold testSum
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e
  · obtain hm|hl|hr := edge_bad_cases C embed a e he
    · simp only [ite_eq_left he,ite_eq_left hm]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hl]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hr]; split_ifs <;> norm_num
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

omit [Fintype V] [Inhabited A] in
lemma matching_sum_bound :
    testSum (fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),())) ≤
      (Fintype.card (Node C):ℝ)*testRate ((matchingCSP C embed).Bad a) := by
  let e : E ↪ Node C × Unit :=
    { toFun e := (dartEmbed C embed (e,false),())
      inj' := by intro e f h; exact congrArg Prod.fst ((dartEmbed C embed).injective (congrArg Prod.fst h)) }
  have h := testSum_injection e (p := fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()))
    (q := (matchingCSP C embed).Bad a) (fun _ h => h)
  simpa only [testSum_card_rate,Fintype.card_prod,Fintype.card_unit,mul_one] using h

omit [Fintype V] in
theorem regular_sound : C.rejection (decoded C a) ≤
    6*(ExpanderFamily.growth:ℝ)*testRate ((regularCSP C embed).Bad a) := by
  have hsum := old_raw C embed a
  have hmatch := matching_sum_bound C embed a
  have hmis := testSum_injection (dartEmbed C embed) (p := fun d => Disagrees C a (dartEmbed C embed d))
    (q := Disagrees C a) (fun _ h => h)
  have heq := total_disagreements C a
  have hblend := PortCSP.blend_failure (matchingCSP C embed) (equalityCSP C) a
  change testRate ((regularCSP C embed).Bad a)=_ at hblend
  rw [testSum_card_rate] at hsum
  change (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤ _ at hsum
  have hraw : (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤
      3*(Fintype.card (Node C):ℝ)*testRate ((regularCSP C embed).Bad a) := by
    nlinarith only [hsum,hmatch,hmis,heq,hblend]
  have hsize : (Fintype.card (Node C):ℝ) ≤
      2*(ExpanderFamily.growth:ℝ)*Fintype.card E := by
    exact_mod_cast node_card_upper C
  have hnon := testRate_nonneg ((regularCSP C embed).Bad a)
  have he : 0 < (Fintype.card E:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ he).mp
  nlinarith only [hraw,mul_le_mul_of_nonneg_right hsize hnon]

end FlexibleCloud
end MetricKMedian.PCP

end Inline_PCPFlexibleCloud

end OAI
