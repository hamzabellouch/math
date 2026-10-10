import OAI.NumberTheory.CubicMoment.Angular.AngularNoStopNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScaleFirstNoStopTail

namespace OAI

/-! The actual theta transform supplies the angular no-stop estimate.
No metaplectic Voronoi premise is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_scaleFirstOrdinaryNoStopTail_isLittleO_proved (hℓ : ℓ ≠ 0) (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (ξ : ℝ)
      (H T : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X ∧ Real.log X ≤ T X) →
      (fun X => angular_scaleFirstOrdinaryNoStopTail ℓ m ρ ξ (H X) (T X) X (h X))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := angular_scaleFirstTailNoStopRow_finite_bound_proved
    ℓ hℓ m hpnt hMV hMV0 hcap (m+5)
  obtain ⟨K,hK,hheight⟩ := height_window_sum_bound
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro ξ H T h hsetup
  unfold angular_scaleFirstOrdinaryNoStopTail
  apply IsLittleO.fun_sum
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  let g₁ : ℝ → ℝ := fun X => (1+Real.log X)^(m+2)*X^(5/6-3/1600:ℝ)
  let g₂ : ℝ → ℝ := fun X => X^(5/6:ℝ)/(1+Real.log X)^3
  have hg : (fun X => g₁ X+g₂ X) =o[atTop] firstMomentScale :=
    (log_power_powerSaving_isLittleO (m+2) (by norm_num : (0:ℝ) < 3/1600)).add
      cubic_log_saving_isLittleO
  apply IsBigO.trans_isLittleO (g := fun X => g₁ X+g₂ X) ?_ hg
  apply IsBigO.of_bound (K*D*(C+E*2^(m+5)))
  filter_upwards [hsetup,hbound,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hs hb hX hlog
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hL : 1 ≤ 1+Real.log X := by linarith
  have hLpos : 0 < 1+Real.log X := zero_lt_one.trans_le hL
  let B := C*X^(5/6-3/1600:ℝ)+E*X^(5/6:ℝ)/(Real.log X)^(m+5)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let f : ℝ → ℂ := fun U => if U ≤ X^(1/100:ℝ) then
    ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      if distinguishedScaleLength d < X^(69/200:ℝ) then
        scaleFirstTailNoStopRow i ℓ ρ ξ (H X) U X (h X) d else 0 else 0
  have hf (U : ℝ) (hTU : T X ≤ U) (_hUH : U < 2*Real.pi*(H X)) :
      ‖f U‖ ≤ D*(1+Real.log X)^(m+1)*B := by
    dsimp only [f]
    split_ifs with hU
    · have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
          ‖if distinguishedScaleLength d < X^(69/200:ℝ) then
            scaleFirstTailNoStopRow i ℓ ρ ξ (H X) U X (h X) d else 0‖ ≤ (1+Real.log X)*B := by
        split_ifs
        · exact hb i him ξ (H X) U (h X) d (zero_lt_one.trans_le hs.1) (hs.2.2.trans hTU) hU
        · simpa only [norm_zero] using mul_nonneg hLpos.le hB
      have hn : (Fintype.card (Fin i → Fin (normPartitionCount
          (Real.exp primeProductWeights.radius*X))):ℝ) ≤ D*(1+Real.log X)^i := by
        simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero] using hcount X hX
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun d _ => hpiece d)).trans
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      apply (mul_le_mul_of_nonneg_right hn (mul_nonneg hLpos.le hB)).trans
      calc
        D*(1+Real.log X)^i*((1+Real.log X)*B) = D*(1+Real.log X)^(i+1)*B := by rw [pow_succ]; ring
        _ ≤ D*(1+Real.log X)^(m+1)*B := by
          gcongr
    · simpa only [norm_zero] using (show 0 ≤ D*(1+Real.log X)^(m+1)*B by positivity)
  have hh := hheight (H X) (T X) (D*(1+Real.log X)^(m+1)*B) f hs.1
    (hlog.trans hs.2.2) (by positivity) hf
  have hlogH : 1+Real.log (H X) ≤ 1+Real.log X :=
    add_le_add le_rfl (Real.log_le_log (zero_lt_one.trans_le hs.1) hs.2.1)
  have hwhole : ‖angular_scaleFirstOrdinaryNoStopArity ℓ i ρ ξ (H X) (T X) X (h X)‖ ≤
      K*D*(1+Real.log X)^(m+2)*B := by
    apply hh.trans
    calc
      K*(1+Real.log (H X))*(D*(1+Real.log X)^(m+1)*B) ≤
          K*(1+Real.log X)*(D*(1+Real.log X)^(m+1)*B) := by gcongr
      _ = _ := by rw [show m+2=(m+1)+1 by omega,pow_succ]; ring
  -- Three logarithms remain after both finite summations.
  have hnorm := stopped_log_quotient_normalize (m+2) 3 hlog hE
    (Real.rpow_nonneg hXp.le (5/6:ℝ))
  have hg₁ : 0 ≤ g₁ X := by dsimp [g₁]; positivity
  have hg₂ : 0 ≤ g₂ X := by dsimp [g₂]; positivity
  rw [Real.norm_of_nonneg (add_nonneg hg₁ hg₂)]
  apply hwhole.trans
  have hnorm' : (1+Real.log X)^(m+2)*(E*X^(5/6:ℝ)/(Real.log X)^(m+5)) ≤
      (E*2^(m+5))*g₂ X := by
    dsimp only [g₂]
    simpa only [show m+2+3=m+5 by omega,mul_div_assoc] using hnorm
  calc
    _ = K*D*(C*g₁ X+(1+Real.log X)^(m+2)*
        (E*X^(5/6:ℝ)/(Real.log X)^(m+5))) := by dsimp [B,g₁]; ring
    _ ≤ K*D*(C*g₁ X+(E*2^(m+5))*g₂ X) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hnorm') (by positivity)
    _ ≤ K*D*((C+E*2^(m+5))*(g₁ X+g₂ X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hC hg₂,mul_nonneg (show 0 ≤ E*2^(m+5) by positivity) hg₁]
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
