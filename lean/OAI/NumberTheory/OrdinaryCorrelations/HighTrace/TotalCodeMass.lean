import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FirstSlot

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
variable {σ P : Type*} [Fintype σ] [Fintype P] [DecidableEq P]

lemma total_code_mass (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) :
    (∑ x : σ → Option P, ∏ p ∈ support x, W p) ≤
      (Fintype.card σ+1:ℝ)*(Fintype.card σ+1:ℝ)^(Fintype.card σ)*
        (max 1 (∑ p,W p))^(Fintype.card σ) := by
  let N := Fintype.card σ
  let H : ℝ := max 1 (∑ p,W p)
  have hH : 1 ≤ H := le_max_left _ _
  have he := weighted_code_sum (σ:=σ) (fun _ => 1) (by intro; norm_num) W hW
  simp only [one_mul] at he
  apply he.trans
  change (∑ z : (m : Fin (N+1)) × (σ → Option (Fin m.val)) × (Fin m.val → P),
    ∏ i, W (z.2.2 i)) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ m : Fin (N+1), ((N+1:ℝ)^N*H^N) := by
      apply sum_le_sum
      intro m hm
      rw [Fintype.sum_prod_type]
      have hrow : (∑ v : Fin m.val → P, ∏ i, W (v i)) ≤ H^N := by
        rw [←Fintype.prod_sum]
        simp only [prod_const,card_univ,Fintype.card_fin]
        apply (pow_le_pow_left₀ (sum_nonneg (fun p hp => hW p)) (le_max_right (1:ℝ) _) _).trans
        exact pow_le_pow_right₀ hH (Nat.lt_succ_iff.mp m.isLt)
      calc
        _ ≤ ∑ _d : σ → Option (Fin m.val), H^N := sum_le_sum (fun d hd => hrow)
        _ = ((m.val+1:ℕ):ℝ)^N*H^N := by simp [N]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hH) _)
          apply pow_le_pow_left₀ (by positivity)
          have hm' : m.val ≤ N := Nat.lt_succ_iff.mp m.isLt
          exact_mod_cast Nat.add_le_add_right hm' 1
    _ = _ := by simp [N,H]; ring

end OrdinaryCorrelations.SharedSlotPatterns

end

end OAI
