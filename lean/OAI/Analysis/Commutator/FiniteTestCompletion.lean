import Mathlib
import OAI.Analysis.Commutator.PartialWordContinuity
import OAI.Analysis.Commutator.PartialUnitaryCompletion

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

lemma slotCost_le {m : ℕ} (hk : ∀ i,(k i).natAbs ≤ m) (s : Slot K) : slotCost k s ≤ m+2 := by
  cases s with
  | none => simp [slotCost]
  | some s =>
    cases s with
    | none => simp [slotCost]
    | some i => exact Nat.add_le_add_right (hk i) 2

lemma wordCost_le {m : ℕ} (hk : ∀ i,(k i).natAbs ≤ m) (l : List (Letter J K)) :
    wordCost k l ≤ l.length*(m+2) := by
  induction l with
  | nil => simp [wordCost]
  | cons i l ih =>
    have hh := Nat.add_le_add (slotCost_le k hk i.2) ih
    simpa only [wordCost,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,
      one_mul,Nat.add_comm] using hh

include hτ in
lemma momentBound_completed (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v : PartialUnitary A) {N : ℕ} {B C : ℝ}
    (hB : MomentBound τ x k v N B)
    (hpower : ∀ i,((k i).natAbs:ℝ)+2 ≤ C)
    (hword : ∀ l : List (Letter J K),l.length ≤ N → (wordCost k l:ℝ) ≤ C) :
    MomentBound τ x k v.completed N (B+C*Real.sqrt (1-(τ v.support).re)) := by
  have he := v.completion_norm_sub τ hone
  constructor
  · intro i
    have hd : ‖τ (v.completed.power (k i))-τ (v.power (k i))‖ ≤
        C*Real.sqrt (1-(τ v.support).re) := by
      rw [←map_sub]
      exact (TracialL2.norm_trace_le τ hτ hone _).trans
        ((v.completed.power_norm_sub τ hτ v (k i)).trans (by
          rw [he]
          exact mul_le_mul_of_nonneg_right (hpower i) (Real.sqrt_nonneg _)))
    exact (norm_le_insert (τ (v.power (k i))) (τ (v.completed.power (k i)))).trans
      (by simpa only [norm_sub_rev] using add_le_add (hB.1 i) hd)
  · intro l hl hlen hvalid
    have hd : ‖τ (word x k v.completed l)-τ (word x k v l)‖ ≤
        C*Real.sqrt (1-(τ v.support).re) := by
      exact (trace_word_norm_sub τ hτ x k hone hx v.completed v l).trans (by
        rw [he]
        exact mul_le_mul_of_nonneg_right (hword l hlen) (Real.sqrt_nonneg _))
    exact (norm_le_insert (τ (word x k v l)) (τ (word x k v.completed l))).trans
      (by simpa only [norm_sub_rev] using add_le_add (hB.2 l hl hlen hvalid) hd)

omit [StarOrderedRing A] in
lemma momentBound_mono {v : PartialUnitary A} {N : ℕ} {B C : ℝ}
    (hB : MomentBound τ x k v N B) (hBC : B ≤ C) : MomentBound τ x k v N C :=
  ⟨fun i => (hB.1 i).trans hBC,fun l hl hn hv => (hB.2 l hl hn hv).trans hBC⟩

end Kadison.FinitePatching.Words

end

end
end

end OAI
