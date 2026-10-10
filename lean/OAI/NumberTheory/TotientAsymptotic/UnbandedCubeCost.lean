import OAI.NumberTheory.TotientAsymptotic.UnbandedCube
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.RenewalLower
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor

namespace OAI

/-! The additive unit-box cost is uniformly comparable to one renewal coefficient. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma summable_shifted_square_geometric :
    Summable (fun n : ℕ => ((n:ℝ)+1)^2*rho^n) := by
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one rho_pos.le rho_lt_one
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  ext n
  simp only [pow_one]
  ring

theorem prefixCubeCost_normalized_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, prefixCubeCost N*rho^N ≤ C := by
  obtain ⟨K,hK,hg⟩ := (normalizedRenewal_properties fordRenewalInput).2
  let S := ∑' n : ℕ, ((n:ℝ)+1)^2*rho^n
  have hS : 0 < S := by
    have hh := summable_shifted_square_geometric.le_tsum 0
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
    norm_num at hh
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hh
  refine ⟨(1+K)*S, mul_pos (by linarith) hS, fun N => ?_⟩
  have hfirst : (N:ℝ)^2*rho^N ≤ S := by
    apply le_trans _ (summable_shifted_square_geometric.le_tsum N
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _)))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_pos.le _)
    nlinarith [Nat.cast_nonneg N (α:=ℝ)]
  have hsum : (∑ i : Fin N, g (i.val+1)*((N-i.val:ℕ):ℝ)^2)*rho^N ≤ K*S := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin N, K*(((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : i.val+1+(N-i.val-1)=N := by omega
        have he : ((N-i.val:ℕ):ℝ)=((N-i.val-1:ℕ):ℝ)+1 := by
          exact_mod_cast (show N-i.val=N-i.val-1+1 by omega)
        have hh : g (i.val+1)*rho^(i.val+1) ≤ K := by
          have hh := hg (i.val+1)
          rw [Real.norm_eq_abs, abs_of_pos (normalizedRenewal_pos _)] at hh
          exact hh
        have hm := mul_le_mul_of_nonneg_right hh
          (show 0 ≤ (((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) by exact mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
        have hp : rho^N = rho^(i.val+1)*rho^(N-i.val-1) := by
          rw [← pow_add, hi]
        rw [hp, he]
        nlinarith only [hm]
      _ = K*∑ j ∈ Finset.range N, ((j:ℝ)+1)^2*rho^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_bij (fun i _ => N-i.val-1)
        · intro i _
          exact Finset.mem_range.mpr (by omega)
        · intro i _ j _ hij
          apply Fin.ext
          have := i.isLt
          have := j.isLt
          omega
        · intro j hj
          have hj := Finset.mem_range.mp hj
          exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
        · intro i _
          ring
      _ ≤ K*S := mul_le_mul_of_nonneg_left
        (summable_shifted_square_geometric.sum_le_tsum _
          (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))) hK
  unfold prefixCubeCost
  rw [add_mul]
  nlinarith only [hfirst,hsum]

/-- For prefixes ending `H` coordinates before the natural dimension, the
unit-box enlargement has a uniformly bounded relative volume cost. -/
theorem prefixCubeCost_relative_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ N ≤ m x,
      (N:ℝ)*prefixCubeCost N/B x ≤ C*rho^(m x-N) := by
  obtain ⟨A,hA,ha⟩ := prefixCubeCost_normalized_bound
  refine ⟨2*A/lam, div_pos (mul_pos (by norm_num) hA) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound, B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hN
  have hcost : prefixCubeCost N ≤ A/rho^N :=
    (le_div_iff₀ (pow_pos rho_pos N)).mpr (ha N)
  have hNm : (N:ℝ) ≤ m x := by exact_mod_cast hN
  have hp : rho^N*rho^(m x-N)=rho^(m x) := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  calc
    _ ≤ (m x:ℝ)*(A/rho^N)/B x := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul hNm hcost (prefixCubeCost_nonneg N) (Nat.cast_nonneg _)
    _ = A*((m x:ℝ)/(B x*rho^(m x)))*rho^(m x-N) := by
      rw [← hp]
      field_simp [rho_pos.ne']
    _ ≤ A*(2/lam)*rho^(m x-N) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx hA.le) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
