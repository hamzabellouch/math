import OAI.MeasureTheory.Falconer.Estimates.EndpointSelectionLosses
import OAI.MeasureTheory.Falconer.Measures.EndpointMassRatios
import OAI.MeasureTheory.Falconer.Estimates.EndpointRowBudget
import OAI.MeasureTheory.Falconer.Estimates.EndpointDyadicScale
import OAI.MeasureTheory.Falconer.Estimates.DyadicLossAbsorption

namespace OAI

/-! # Simultaneous scalar budgets for the endpoint angular application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem exists_endpoint_angular_parameters {ε₀ c₁ c₂ s a : ℝ}
    (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hgap : 0 < 2*s-3-6*a) (ha : a < 1/2)
    (Cm Large V Cpoint Ccover C H : ℝ) :
    ∃ u ε τ : ℝ, 0 < u ∧ 0 < ε ∧ 0 < τ ∧ ε < ε₀ ∧ ε < u ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        let δ := 1/(2:ℝ)^N
        ((N+1:ℕ):ℝ)*(Cm*δ^(-ε)) ≤ δ^(-u) ∧
        Large ≤ δ^(-u) ∧ Cpoint*δ^(-6*u) ≤ δ^(-40*u) ∧
        V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 ∧
        δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
        δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) ∧
        Ccover*δ^(-1-12*u) ≤ δ^(-1-40*u) ∧
        144*H*δ ≤ 3*(δ^a)^2 ∧
        (δ^(-1-40*u))^3*((6*C+35)/δ^a)^6*(δ^(-40*u)*(6*δ)^s)^2 < (δ^(40*u))^2 := by
  obtain ⟨u,τ,hu,hτ,huε,huτ,hc₁',hc₂',hug⟩ :=
    exists_endpoint_selection_losses hε₀ hc₁ hc₂ hgap
  let ε := u/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεu : ε < u := by dsimp [ε]; linarith
  have hεε₀ : ε < ε₀ := hεu.trans huε
  have hdepth := eventually_dyadic_loss_absorption hεu Cm
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -u < 0 by linarith)).eventually
    (eventually_ge_atTop Large)
  have hcoef := eventually_const_mul_rpow_lt (show -40*u < -6*u by linarith) Cpoint
  have hbase := eventually_endpoint_row_base hu hc₁' hc₂' V
  have hmass := eventually_endpoint_mass_thresholds hu huτ
  have hcover := eventually_const_mul_rpow_lt (show -1-40*u < -1-12*u by linarith) Ccover
  have herr := eventually_const_mul_rpow_lt (show (0:ℝ) < 1-2*a by linarith) (48*H)
  have hcount := eventually_endpoint_count_budget
    (s := s) (a := a) (κ := 40*u) (by nlinarith [hug]) C
  have hready := hdepth.and (hlarge.and (hcoef.and (hbase.and (hmass.and
    (hcover.and (herr.and hcount))))))
  have hn := dyadic_inverse_tendsto.eventually hready
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hn
  refine ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,N₀,?_⟩
  intro N hN
  rcases hN₀ N hN with ⟨hd,hL,hC,hB,hM,hT,hE,hF⟩
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨?_,hL,hC.2.le,hB.2,hM.2.1,hM.2.2,hT.2.le,?_,by simpa only [neg_mul] using hF.2⟩
  · have hh := hd.2
    rw [dyadic_log_depth N] at hh
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hh
  · have hp : δ^(1-2*a)*(δ^a)^2 = δ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le,← Real.rpow_add hδ]
      norm_num only [Nat.cast_ofNat]
      rw [show 1-2*a+a*(2:ℝ) = 1 by ring,Real.rpow_one]
    have hh := mul_lt_mul_of_pos_right hE.2 (sq_pos_of_pos (Real.rpow_pos_of_pos hδ a))
    have heq : (48*H)*δ^(1-2*a)*(δ^a)^2 = (48*H)*δ := by rw [mul_assoc,hp]
    rw [Real.rpow_zero,one_mul,heq] at hh
    nlinarith

end Falconer

end OAI
