import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ActualClassLaw

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]
local instance restrictionFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

lemma ordered_restriction_budget {N m : ℕ} (hm : m≤N)
    (p : Law Ω) (θ : Ω→Θ) (F : Ω→Fin N→α)
    (D : Θ→Fin N→Finset α) (J : ℝ)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (θ x) i)
    (hJ : ∀ z i,log (D z i).card≤J)
    (S : Θ→Finset (Fin N))
    (hcard : ∀ z,(p.map θ).mass z≠0→(S z).card=m) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple S hm θ F))))≤
    ∑ z,(p.map θ).mass z*((N:ℝ)*J-entropy ((p.cond θ z).map F)) := by
  have hord : (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple S hm θ F))))=selectedDeficit p θ F S J := by
    convert ordered_deficit p θ F S hm hcard J using 1
    congr!
  rw [hord]
  unfold selectedDeficit
  apply sum_le_sum
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp only [hz,zero_mul,le_refl]
  · apply mul_le_mul_of_nonneg_left _ ((p.map θ).nonneg z)
    have hcap : ∀ i,entropy (((p.cond θ z).map F).marginal i)≤J := by
      intro i
      change entropy (((p.cond θ z).map F).map (fun f=>f i))≤J
      rw [Law.map_map]
      apply (entropy_mapped_support (p.cond θ z) (fun x=>F x i) (D z i) ?_).trans (hJ z i)
      intro x hx
      obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
      simpa only [←he] using hD x hx i
    have hh := (subset_budget_deficit ((p.cond θ z).map F) (S z) (fun _=>J) hcap).2
    simpa only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] using hh
end
end SharpLogRamsey.Selection

end

end OAI
