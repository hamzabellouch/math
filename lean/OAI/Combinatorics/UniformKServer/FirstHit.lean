import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

                               
section
namespace UniformKServer.FirstHit
noncomputable section
open FiniteProbability
attribute [local instance] Classical.propDecidable

/-- A finite independently sampled chronological family. Each coordinate can
include a collapsed continuous radius law, so no count of random bits is
claimed at this existence-only stage. -/
structure Entry where
  Sample : Type
  finite : Fintype Sample
  law : @Law Sample finite
  hit : Sample → Bool
  separates : Sample → Bool
  separates_hit : ∀ x, separates x = true → hit x = true

attribute [instance] Entry.finite

def Samples : List Entry → Type
  | [] => Unit
  | E::es => E.Sample × Samples es

instance samplesFinite : (es : List Entry) → Fintype (Samples es)
  | [] => inferInstanceAs (Fintype Unit)
  | E::es => @instFintypeProd _ _ E.finite (samplesFinite es)

def experiment : (es : List Entry) → Law (Samples es)
  | [] => ⟨fun _ => 1,by intro _; norm_num,by change (∑ _ : Unit, (1:ℝ)) = 1; simp⟩
  | E::es => E.law.prod (experiment es)

def firstSeparates : (es : List Entry) → Samples es → Bool
  | [], _ => false
  | E::es, ω => if E.hit ω.1 then E.separates ω.1 else firstSeparates es ω.2

def hitProbability (E : Entry) : ℝ := E.law.expect (fun ω => if E.hit ω then 1 else 0)
def separationProbability (E : Entry) : ℝ := E.law.expect (fun ω => if E.separates ω then 1 else 0)
theorem hitProbability_bounds (E : Entry) : hitProbability E ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact E.law.expect_nonneg _ (fun _ => by split_ifs <;> norm_num)
  · have := E.law.expect_mono (fun ω => if E.hit ω then 1 else 0) (fun _ => 1)
      (fun _ => by split_ifs <;> norm_num)
    simpa only [hitProbability,Law.expect_const] using this

theorem recurrence (E : Entry) (es : List Entry) :
    (experiment (E::es)).expect (fun ω => if firstSeparates (E::es) ω then 1 else 0) =
      separationProbability E+(1-hitProbability E)*
        (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0) := by
  let z := (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0)
  let f : E.Sample → Samples es → ℝ := fun ω η =>
    if (if E.hit ω then E.separates ω else firstSeparates es η) then 1 else 0
  change (E.law.prod (experiment es)).expect (fun ω => f ω.1 ω.2) = _
  rw [E.law.expect_prod (experiment es) f]
  have hinner (ω : E.Sample) :
      (experiment es).expect (f ω) =
      (if E.separates ω then 1 else 0)+(1-(if E.hit ω then 1 else 0))*z := by
    unfold f
    by_cases hh : E.hit ω = true
    · simp only [ite_eq_left hh,sub_self,zero_mul,add_zero,Law.expect_const]
    · have hs : E.separates ω ≠ true := fun h => hh (E.separates_hit ω h)
      simp only [ite_eq_right hh,ite_eq_right hs,sub_zero,one_mul,zero_add]
      rfl
  rw [E.law.expect_congr _ _ hinner,E.law.expect_add]
  have hid : E.law.expect (fun ω => (1-(if E.hit ω then 1 else 0))*z) =
      (1-hitProbability E)*z := by
    rw [show (fun ω => (1-(if E.hit ω then 1 else 0))*z) =
        (fun ω => z*(1-(if E.hit ω then 1 else 0))) by funext; ring]
    rw [E.law.expect_mul,E.law.expect_sub,E.law.expect_const]
    unfold hitProbability
    ring
  rw [hid]
  rfl
/-- First-hit bound with no factor for the number of entries multiplying the
main density term. The only count loss is on the truncated tail correction. -/
theorem first_hit_bound (es : List Entry) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hlocal : ∀ E ∈ es, separationProbability E ≤ α*(hitProbability E+ε)) :
    (experiment es).expect (fun ω => if firstSeparates es ω then 1 else 0) ≤
      α*(1+(es.length:ℝ)*ε)
 := by
  induction es with
  | nil =>
    have he : (experiment []).expect (fun ω => if firstSeparates [] ω then (1:ℝ) else 0) = 0 := by
      exact Law.expect_const _ 0
    rw [he,List.length_nil,Nat.cast_zero,zero_mul,add_zero, mul_one]
    exact hα
  | cons E es ih =>
    rw [recurrence]
    obtain ⟨hp0,hp1⟩ := hitProbability_bounds E
    have hs := hlocal E (List.mem_cons_self ..)
    have hi := ih (fun E hE => hlocal E (List.mem_cons_of_mem _ hE))
    have hm := mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ 1-hitProbability E)
    calc
      _ ≤ α*(hitProbability E+ε)+(1-hitProbability E)*(α*(1+(es.length:ℝ)*ε)) := add_le_add hs hm
      _ = α*(1+((es.length:ℝ)+1)*ε)-α*hitProbability E*(es.length:ℝ)*ε := by ring
      _ ≤ α*(1+((es.length:ℝ)+1)*ε) := sub_le_self _ (by positivity : 0 ≤ α*hitProbability E*(es.length:ℝ)*ε)
      _ = _ := by rw [List.length_cons,Nat.cast_add,Nat.cast_one]
end
end UniformKServer.FirstHit

end


end OAI
