import Mathlib
import OAI.Combinatorics.KMedian.Amplification.RegularizationObjects
import OAI.Combinatorics.KMedian.Amplification.TestSum

namespace OAI

section Inline_PCPRegularizationSound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
  [Inhabited A] [Nonempty E]
variable (C : BinaryCSP V E A) (a : Node C → A)

def Disagrees (n : Node C) : Prop := a n ≠ decoded C a n.1.val

omit [Nonempty E] in
lemma cloud_raw (v : Active C) :
    (Fintype.card ExpanderFamily.Degree : ℝ)*testSum (fun w : Copy C v => Disagrees C a ⟨v,w⟩) ≤
      2*testSum (fun p : Copy C v × ExpanderFamily.Degree =>
        (equalityCSP C).Bad a (⟨v,p.1⟩,p.2)) := by
  have h := cloud_sound C a v
  have he := testRate_congr (fun p : Copy C v × ExpanderFamily.Degree => equality_bad C a v p.1 p.2)
  rw [testSum_card_rate,testSum_card_rate,he]
  simp only [Fintype.card_prod,Nat.cast_mul]
  unfold PortGraph.equalityFailure at h
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤
    (Fintype.card ExpanderFamily.Degree:ℝ)*Fintype.card (Copy C v) by positivity)
  dsimp only [Disagrees]
  simp only [Fintype.card_prod,Nat.cast_mul] at hh
  nlinarith only [hh]

omit [Inhabited A] [Nonempty E] in
lemma equality_raw_partition :
    testSum ((equalityCSP C).Bad a) =
      ∑ v : Active C, testSum (fun p : Copy C v × ExpanderFamily.Degree =>
        (equalityCSP C).Bad a (⟨v,p.1⟩,p.2)) := by
  simp only [testSum,Fintype.sum_prod_type,Fintype.sum_sigma]

lemma total_disagreements :
    testSum (Disagrees C a) ≤
      2*(Fintype.card (Node C):ℝ)*testRate ((equalityCSP C).Bad a) := by
  have h := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Active C))) => cloud_raw C a v)
  rw [← mul_sum,← mul_sum,← equality_raw_partition C a,← testSum_sigma] at h
  have he : testSum ((equalityCSP C).Bad a) =
      (Fintype.card (Node C):ℝ)*Fintype.card ExpanderFamily.Degree *
        testRate ((equalityCSP C).Bad a) := by
    rw [testSum_card_rate,Fintype.card_prod,Nat.cast_mul]
  rw [he] at h
  have hd : 0 < (Fintype.card ExpanderFamily.Degree:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [h]

omit [Nonempty E] in
lemma edge_bad_cases (e : E)
    (he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) :
    (matchingCSP C).Bad a (dartEmbed C (e,false),()) ∨
      Disagrees C a (dartEmbed C (e,false)) ∨ Disagrees C a (dartEmbed C (e,true)) := by
  by_contra h
  simp only [not_or] at h
  have hl : a (dartEmbed C (e,false))=decoded C a (C.left e) := by
    exact not_ne_iff.mp h.2.1
  have hr : a (dartEmbed C (e,true))=decoded C a (C.right e) := by
    exact not_ne_iff.mp h.2.2
  exact he (by
    have hh := h.1
    rw [matching_bad] at hh
    simpa only [not_not,hl,hr] using hh)

omit [Nonempty E] in
lemma old_raw :
    testSum (fun e => (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) ≤
      testSum (fun e => (matchingCSP C).Bad a (dartEmbed C (e,false),())) +
        testSum (fun d : Dart (E := E) => Disagrees C a (dartEmbed C d)) := by
  unfold testSum
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e
  · obtain hm|hl|hr := edge_bad_cases C a e he
    · simp only [ite_eq_left he,ite_eq_left hm]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hl]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hr]; split_ifs <;> norm_num
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

omit [Inhabited A] in
lemma matching_sum_bound :
    testSum (fun e => (matchingCSP C).Bad a (dartEmbed C (e,false),())) ≤
      (Fintype.card (Node C):ℝ)*testRate ((matchingCSP C).Bad a) := by
  let e : E ↪ Node C × Unit :=
    { toFun e := (dartEmbed C (e,false),())
      inj' := by intro e f h; exact congrArg Prod.fst ((dartEmbed C).injective (congrArg Prod.fst h)) }
  have h := testSum_injection e (p := fun e => (matchingCSP C).Bad a (dartEmbed C (e,false),()))
    (q := (matchingCSP C).Bad a) (fun _ h => h)
  simpa only [testSum_card_rate,Fintype.card_prod,Fintype.card_unit,mul_one] using h

theorem regular_sound : C.rejection (decoded C a) ≤
    6*(ExpanderFamily.growth:ℝ)*testRate ((regularCSP C).Bad a) := by
  have hsum := old_raw C a
  have hmatch := matching_sum_bound C a
  have hmis := testSum_injection (dartEmbed C) (p := fun d => Disagrees C a (dartEmbed C d))
    (q := Disagrees C a) (fun _ h => h)
  have heq := total_disagreements C a
  have hblend := PortCSP.blend_failure (matchingCSP C) (equalityCSP C) a
  change testRate ((regularCSP C).Bad a)=_ at hblend
  rw [testSum_card_rate] at hsum
  change (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤ _ at hsum
  have hraw : (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤
      3*(Fintype.card (Node C):ℝ)*testRate ((regularCSP C).Bad a) := by
    nlinarith only [hsum,hmatch,hmis,heq,hblend]
  have hsize : (Fintype.card (Node C):ℝ) ≤
      2*(ExpanderFamily.growth:ℝ)*Fintype.card E := by
    exact_mod_cast node_card_upper C
  have hnon := testRate_nonneg ((regularCSP C).Bad a)
  have he : 0 < (Fintype.card E:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ he).mp
  nlinarith only [hraw,mul_le_mul_of_nonneg_right hsize hnon]

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationSound

end OAI
