import Mathlib
import OAI.Combinatorics.UniformKServer.FirstHit

namespace OAI

                                      
section

/-! Required finite-law partition bridge: only potentially hitting roster
records are charged in the truncated-radius correction. All other present
records remain in the actual chronological product experiment. -/
namespace UniformKServer.FirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable

theorem separationProbability_nonneg (E : Entry) : 0 ≤ separationProbability E :=
  E.law.expect_nonneg _ (fun _ => by split_ifs <;> norm_num)

theorem separationProbability_le_hit (E : Entry) :
    separationProbability E ≤ hitProbability E :=
  by
    apply E.law.expect_mono
    intro ω
    by_cases hs : E.separates ω = true
    · simp only [ite_eq_left hs, ite_eq_left (E.separates_hit ω hs)]
      exact le_rfl
    · simp only [ite_eq_right hs]
      split_ifs <;> norm_num

/-- A support-sensitive version of the first-hit telescope. The main term
still telescopes to one; only the sum of tail errors is charged. -/
theorem first_hit_error_sum (es : List Entry) (α : ℝ) (ε : Entry → ℝ)
    (hα : 0 ≤ α) (hε : ∀ E ∈ es, 0 ≤ ε E)
    (hlocal : ∀ E ∈ es, separationProbability E ≤ α*(hitProbability E+ε E)) :
    (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0) ≤
      α*(1+(es.map ε).sum) := by
  induction es with
  | nil =>
    simpa only [experiment, firstSeparates, Bool.false_eq_true, ite_false,
      Law.expect_const, List.map_nil, List.sum_nil, add_zero, mul_one] using hα
  | cons E es ih =>
    rw [recurrence]
    obtain ⟨hp0,hp1⟩ := hitProbability_bounds E
    have hs := hlocal E (List.mem_cons_self ..)
    have hi := ih (fun F hF => hε F (List.mem_cons_of_mem _ hF))
      (fun F hF => hlocal F (List.mem_cons_of_mem _ hF))
    have hm := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hp1)
    have ht : 0 ≤ (es.map ε).sum := List.sum_nonneg (by
      intro a ha
      obtain ⟨F,hF,rfl⟩ := List.mem_map.mp ha
      exact hε F (List.mem_cons_of_mem _ hF))
    calc
      _ ≤ α*(hitProbability E+ε E)+(1-hitProbability E)*(α*(1+(es.map ε).sum)) :=
        add_le_add hs hm
      _ = α*(1+ε E+(es.map ε).sum)-α*hitProbability E*(es.map ε).sum := by ring
      _ ≤ α*(1+ε E+(es.map ε).sum) :=
        sub_le_self _ (mul_nonneg (mul_nonneg hα hp0) ht)
      _ = _ := by simp only [List.map_cons,List.sum_cons]; ring

/-- A heterogeneous indexed formulation avoids identifying equal physical
centers or equal entry laws; repeated centers are counted as separate records. -/
theorem first_hit_support {I : Type*} (is : List I) (entry : I → Entry)
    (P : I → Prop) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hlocal : ∀ i ∈ is, P i →
      separationProbability (entry i) ≤ α*(hitProbability (entry i)+ε))
    (hmiss : ∀ i ∈ is, ¬ P i → hitProbability (entry i) = 0) :
    (experiment (is.map entry)).expect (fun ω => if firstSeparates _ ω then 1 else 0) ≤
      α*(1+((is.filter (fun i => decide (P i))).length:ℝ)*ε) := by
  induction is with
  | nil =>
    have he : (experiment []).expect (fun ω => if firstSeparates [] ω then (1:ℝ) else 0) = 0 :=
      Law.expect_const _ 0
    change (experiment []).expect (fun ω => if firstSeparates [] ω then (1:ℝ) else 0) ≤ _
    rw [he,List.filter_nil,List.length_nil,Nat.cast_zero,zero_mul,add_zero,mul_one]
    exact hα
  | cons i is ih =>
    change (experiment (entry i :: is.map entry)).expect
      (fun ω => if firstSeparates (entry i :: is.map entry) ω then 1 else 0) ≤ _
    have hre := recurrence (entry i) (is.map entry)
    rw [hre]
    obtain ⟨hp0,hp1⟩ := hitProbability_bounds (entry i)
    have hi := ih (fun j hj => hlocal j (List.mem_cons_of_mem _ hj))
      (fun j hj => hmiss j (List.mem_cons_of_mem _ hj))
    by_cases hp : P i
    · have hs := hlocal i (List.mem_cons_self ..) hp
      have hm := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hp1)
      simp only [List.filter_cons,decide_eq_true_eq,ite_eq_left hp,List.length_cons,
        Nat.cast_add,Nat.cast_one]
      calc
        _ ≤ α*(hitProbability (entry i)+ε)+(1-hitProbability (entry i))*
            (α*(1+((is.filter (fun i => decide (P i))).length:ℝ)*ε)) := add_le_add hs hm
        _ = α*(1+(((is.filter (fun i => decide (P i))).length:ℝ)+1)*ε)-
            α*hitProbability (entry i)*((is.filter (fun i => decide (P i))).length:ℝ)*ε := by ring
        _ ≤ _ := sub_le_self _ (by positivity)
    · have hh := hmiss i (List.mem_cons_self ..) hp
      have hs : separationProbability (entry i) = 0 :=
        le_antisymm (by rw [←hh]; exact separationProbability_le_hit _) (separationProbability_nonneg _)
      simpa only [List.filter_cons,decide_eq_true_eq,ite_eq_right hp,hh,hs,sub_zero,
        one_mul,zero_add] using hi

end
end UniformKServer.FirstHit

end

end OAI
