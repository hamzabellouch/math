import OAI.Probability.ClassicalON.ResponseTransfer

namespace OAI

noncomputable section
open Set
open scoped BigOperators ComplexConjugate
namespace ClassicalON

theorem squareTheta_compact : HasCompactSupport squareTheta := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareTheta_zero
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

theorem theta_lipschitz_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
    |squareTheta w-squareTheta z| ≤ C*‖w-z‖ := by
  obtain ⟨C,hC,_,hL⟩ := smooth_compact_lipschitz_bound squareTheta_compact squareTheta_contDiff
  exact ⟨C,hC,by simpa only [Real.norm_eq_abs] using hL⟩

namespace LatticeGraph

theorem theta_edge_bounds : ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧
    ∀ (G : LatticeGraph) (k : ℕ), 4 ≤ k → ∀ e : G.edges,
      |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3 := by
  obtain ⟨L,hL,hLip⟩ := theta_lipschitz_bound
  obtain ⟨D,hD,hR⟩ := squareTheta_step_error
  refine ⟨L,D,hL,hD,?_⟩
  intro G k hk e
  constructor
  · have h := hLip (scaledSite k e.val.1.val) (scaledSite k e.val.2.val)
    rw [G.scaled_edge_distance] at h
    exact h.trans_eq (by ring)
  · have hN : (16:ℝ) ≤ (2:ℝ)^k := by
      calc (16:ℝ) = (2:ℝ)^4 := by norm_num
           _ ≤ _ := pow_le_pow_right₀ (by norm_num) hk
    have hmesh : |1/(2:ℝ)^k| ≤ 1/16 := by
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) hN
    have h := hR (G.edgeDirection e) (scaledSite k e.val.1.val) (1/(2:ℝ)^k) hmesh
    rw [← scaledSite_add_axis, ← G.edge_step e,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)] at h
    simpa only [thetaEdge,profileEdge,div_pow,one_pow,mul_one_div] using h

theorem theta_sum_bounds (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k)
    (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ 512*D/(2:ℝ)^k ∧
    (∑ e, |G.thetaEdge k e|^2) ≤ 512*L^2 ∧
    (∑ e, |G.thetaEdge k e-G.profileEdge k e| *
      (|G.thetaEdge k e| + |G.profileEdge k e|)) ≤ 512*D*(2*L+D)/((2:ℝ)^k)^2 := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hcount := G.edge_card_bound k hG
  change (Fintype.card G.edges:ℝ) ≤ 512*N^2 at hcount
  have hv (e : G.edges) : |G.profileEdge k e| ≤ (L+D)/N := by
    have htri : |G.profileEdge k e| ≤ |G.thetaEdge k e| + |G.thetaEdge k e-G.profileEdge k e| := by
      simpa only [add_sub_cancel, abs_sub_comm] using abs_add_le (G.thetaEdge k e) (G.profileEdge k e-G.thetaEdge k e)
    have hpow : N ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
    calc _ ≤ L/N+D/N^3 := htri.trans (add_le_add (he e).1 (he e).2)
         _ ≤ L/N+D/N := add_le_add_right (div_le_div_of_nonneg_left hD hN hpow) _
         _ = _ := by ring
  have hs1 : (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ (Fintype.card G.edges:ℝ)*(D/N^3) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun e _ => (he e).2)
  have hs2 : (∑ e, |G.thetaEdge k e|^2) ≤ (Fintype.card G.edges:ℝ)*(L/N)^2 := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => pow_le_pow_left₀ (abs_nonneg _) (he e).1 2)
  have hs3 : (∑ e, |G.thetaEdge k e-G.profileEdge k e| *(|G.thetaEdge k e| + |G.profileEdge k e|)) ≤
      (Fintype.card G.edges:ℝ)*(D/N^3*((2*L+D)/N)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => mul_le_mul (he e).2 (show |G.thetaEdge k e| + |G.profileEdge k e| ≤ (2*L+D)/N from
        (add_le_add (he e).1 (hv e)).trans_eq (by ring)) (by positivity) (by positivity))
  refine ⟨hs1.trans ?_,hs2.trans ?_,hs3.trans ?_⟩
  all_goals
    calc _ ≤ 512*N^2*_ := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = _ := by dsimp only [N]; field_simp

end LatticeGraph
end ClassicalON

end

end OAI
