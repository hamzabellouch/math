import Mathlib
import OAI.Analysis.Commutator.ExponentialMomentBudget
import OAI.Analysis.Commutator.PartialWordPerturbation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

omit [StarOrderedRing A] in
lemma zero_word_trace (hcenter : ∀ j,τ (x j)=0) (l : List (Letter J K))
    (hne : l≠[]) (hv : Valid l) : τ (word x k PartialUnitary.zero l)=0 := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons i l =>
    cases l with
    | nil =>
      rcases i with ⟨j,s⟩
      cases s with
      | none => simpa [letter,slotPower] using hcenter j
      | some s =>
        cases s <;> simp only [word_cons,word_nil,letter,slotPower,PartialUnitary.zero_power,
          mul_zero,mul_one,map_zero]
        simp [PartialUnitary.zero]
    | cons j l =>
      obtain ⟨a,ha⟩ := hv [] i (j::l) rfl (by simp)
      simp [word_cons,letter,ha,slotPower]

omit [StarOrderedRing A] in
lemma zero_momentBound (hcenter : ∀ j,τ (x j)=0) (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    MomentBound τ x k PartialUnitary.zero N B := by
  constructor
  · intro i; simpa using hB
  · intro l hl hlen hv
    simpa only [zero_word_trace τ x k hcenter l hl hv,norm_zero] using hB

include hτ in
theorem momentBound_add (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re))
    (hpure : ∀ i,‖τ (w.power (k i))‖ ≤ ε*(τ w.support).re)
    (hsmall : ∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        ε^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ ε*(τ w.support).re) :
    MomentBound τ x k (v.add w horth) N
      (momentBudget ε (budgetSlope N η) (τ (v.add w horth).support).re) := by
  have ht : 0 ≤ (τ v.support).re := (τ.map_nonneg v.projection.nonneg).1
  have hq : 0 ≤ (τ w.support).re := (τ.map_nonneg w.projection.nonneg).1
  have he : (τ (v.add w horth).support).re=(τ v.support).re+(τ w.support).re := by
    change (τ (v.support+w.support)).re=_
    rw [map_add,Complex.add_re]
  constructor
  · intro i
    rw [v.add_power w horth,map_add]
    exact (norm_add_le _ _).trans ((add_le_add (hbound.1 i) (hpure i)).trans
      (by rw [he]; exact pure_momentBudget_step hε hη ht hq N))
  · intro l hl hlen hv
    have hh := word_perturbation_bound τ hτ x k hx v w horth hqp
      (momentBudget_nonneg hε _ _) hε hη hrest hbound hsmall hphase l hlen hv
    calc
      _ ≤ ‖τ (word x k v l)‖+‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ := by
        simpa only [norm_sub_rev] using norm_le_insert (τ (word x k v l))
          (τ (word x k (v.add w horth) l))
      _ ≤ momentBudget ε (budgetSlope N η) (τ v.support).re+
          ((l.length:ℝ)+(l.length:ℝ)^2)*
            (ε+2*momentBudget ε (budgetSlope N η) (τ v.support).re/η)*(τ w.support).re :=
        add_le_add (hbound.2 l hl hlen hv) hh
      _ ≤ _ := by rw [he]; exact word_momentBudget_step hε hη ht hq hlen

end Kadison.FinitePatching.Words

end

end
end

end OAI
