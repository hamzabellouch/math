import Mathlib
import OAI.Combinatorics.UniformKServer.FinitePiLaw
import OAI.Combinatorics.UniformKServer.FirstHit

namespace OAI

                                 
section

/-! Chronological first-hit experiments are the actual marginal of one fixed
independent tape; no product-law identity is supplied as a hypothesis. -/
noncomputable section
namespace UniformKServer.FirstHit
open FiniteProbability
open scoped Classical
variable {I : Type*} [Fintype I]

def firstPi (E : I → Entry) : List I → (∀ i, (E i).Sample) → Bool
  | [], _ => false
  | i::is, ω => if (E i).hit (ω i) then (E i).separates (ω i) else firstPi E is ω

omit [Fintype I] in
theorem firstPi_dep (E : I → Entry) (is : List I) (ω η : ∀ i, (E i).Sample)
    (he : ∀ i ∈ is, ω i=η i) : firstPi E is ω=firstPi E is η := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [firstPi,he i (List.mem_cons_self ..),ih (fun j hj => he j (List.mem_cons_of_mem _ hj))]

theorem pi_recurrence (E : I → Entry) (i : I) (is : List I) (hi : i ∉ is) :
    (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E (i::is) ω then 1 else 0)=
    separationProbability (E i)+(1-hitProbability (E i))*
      (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E is ω then 1 else 0) := by
  have hid (ω : ∀ j, (E j).Sample) :
      (if firstPi E (i::is) ω then (1:ℝ) else 0)=
      (if (E i).separates (ω i) then 1 else 0)+
        (1-(if (E i).hit (ω i) then 1 else 0))*(if firstPi E is ω then 1 else 0) := by
    by_cases hh : (E i).hit (ω i)=true
    · simp only [firstPi,ite_eq_left hh,sub_self,zero_mul,add_zero]
    · have hs : (E i).separates (ω i) ≠ true := fun hs => hh ((E i).separates_hit _ hs)
      simp only [firstPi,ite_eq_right hh,ite_eq_right hs,sub_zero,one_mul,zero_add]
  rw [Law.expect_congr _ _ _ hid,Law.expect_add,
    Law.expect_pi_coordinate (fun j => (E j).law) i (fun a => if (E i).separates a then 1 else 0)]
  rw [Law.expect_pi_separate (fun j => (E j).law) i
    (fun a => 1-(if (E i).hit a then 1 else 0))
    (fun ω => if firstPi E is ω then 1 else 0)]
  · simp only [Law.expect_sub,Law.expect_const,hitProbability,separationProbability]
  · intro ω η he
    have hh : firstPi E is ω=firstPi E is η := by
      apply firstPi_dep
      intro j hj
      exact he j (fun h => hi (h ▸ hj))
    rw [hh]

theorem pi_expect_first (E : I → Entry) (is : List I) (hn : is.Nodup) :
    (Law.pi (fun i => (E i).law)).expect (fun ω => if firstPi E is ω then 1 else 0)=
    (experiment (is.map E)).expect (fun ω => if firstSeparates _ ω then 1 else 0) := by
  induction is with
  | nil =>
    change (Law.pi (fun i => (E i).law)).expect (fun _ => (0:ℝ))=(experiment []).expect (fun _ => 0)
    rw [Law.expect_const,Law.expect_const]
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    rw [pi_recurrence E i is hi,List.map_cons,recurrence,ih hn]

end UniformKServer.FirstHit

end


end

end OAI
