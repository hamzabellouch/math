import OAI.NumberTheory.TotientAsymptotic.LocalOriginalExceptions
import OAI.NumberTheory.TotientAsymptotic.CandidateProperties

namespace OAI

/-! Arithmetic properties of the candidates retained by the local construction. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma local_normal_candidate_pos {x c : ℝ} {d L H b : ℕ}
    (hb : b∈localNormalCandidates x c d L H) : 0<b := by
  obtain ⟨p,q,he,hp,_hq,hnormal,_htail⟩ := local_normal_candidate_representation hb
  rw [he]
  apply Nat.mul_pos hnormal.1.pos
  exact Finset.prod_pos (fun i _ => (local_regular_normality hp i i le_rfl).1.pos)

theorem local_normal_candidate_arithmetic {c : ℝ} (hc : 0<c)
    (d : ℕ) (hd : 0<d) (L : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ b∈localNormalCandidates x c d L H,
        0<b ∧ ((d*b.totient:ℕ):ℝ)≤x ∧ (b:ℝ)/b.totient≤K := by
  refine ⟨Real.exp (1+2*((1-rho)⁻¹/(c/2))),Real.exp_pos _,?_⟩
  filter_upwards [local_normal_candidate_normality_and_value hc d hd L,
    raw_candidate_ratio_bound hc d hd] with H hvalue hratio
  filter_upwards [hvalue,hratio] with x hvalue hratio
  intro b hb
  exact ⟨local_normal_candidate_pos hb,(hvalue b hb).1,
    hratio b (local_regular_candidates_subset (local_normal_candidates_subset hb))⟩

end TotientAsymptotic

end

end OAI
