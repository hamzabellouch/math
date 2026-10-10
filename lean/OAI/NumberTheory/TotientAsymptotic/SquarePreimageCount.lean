import OAI.NumberTheory.TotientAsymptotic.LargeSquareCount

namespace OAI

/-! Large-square exceptions may occur in any preimage of a totient value. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma large_square_preimage_count (N K : ℕ) (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n ≤ N ∧ n.totient=v ∧
      ∃ d : ℕ,K < d ∧ d^2 ∣ n) :
    (Q.card:ℝ) ≤ 2*N/(K+1:ℕ) := by
  classical
  let A := (Finset.Icc 1 N).filter (fun n => ∃ d : ℕ,K < d ∧ d^2 ∣ n)
  have hsub : Q ⊆ A.image Nat.totient := by
    intro v hv
    obtain ⟨n,hn,hN,hφ,hd⟩ := hQ v hv
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn,hN⟩,hd⟩,hφ⟩
  have hc : (Q.card:ℝ) ≤ A.card :=
    Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
  exact hc.trans (large_square_count N K A (by
    intro n hn
    obtain ⟨hn,hd⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2,hd⟩))

/-- Uniformly counts values with a repeated large factor in some preimage.
The log-log preimage bound applies to every preimage, so no least-preimage
choice or fiber bound is involved. -/
theorem square_preimage_exception_count : ∃ C : ℝ,0 < C ∧
    ∀ x : ℝ,Real.exp (Real.exp 1) ≤ x → ∀ K : ℕ,∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
      ∃ d : ℕ,K < d ∧ d^2 ∣ n) →
    (Q.card:ℝ) ≤ C*x*B x/(K+1:ℕ) := by
  obtain ⟨C,hC,hbound⟩ := preimage_loglog_bound
  refine ⟨2*C,by positivity,?_⟩
  intro x hx K Q hQ
  have hpositive : 0 ≤ C*x*B x := by
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
    have hBx : 1 ≤ B x := by
      have hh := Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
      rw [Real.log_exp] at hh
      have hlogx : 0 < Real.log x := (Real.exp_pos 1).trans_le hh
      have ht := Real.log_le_log (Real.exp_pos 1) hh
      simpa only [B,Real.log_exp] using ht
    positivity
  have hb := large_square_preimage_count ⌊C*x*B x⌋₊ K Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hd⟩ := hQ v hv
    refine ⟨n,hn,Nat.le_floor ?_,hφ,hd⟩
    exact hbound x hx n hn (by rwa [hφ]))
  calc
    _ ≤ 2*(⌊C*x*B x⌋₊:ℝ)/(K+1:ℕ) := hb
    _ ≤ 2*(C*x*B x)/(K+1:ℕ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hpositive) (by norm_num)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
