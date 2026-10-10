import OAI.NumberTheory.JointDickman.Counting.SmallArcEnergy
import OAI.NumberTheory.JointDickman.Amplification.MajorArcApproximation

namespace OAI

/-! # The coefficient model on the retained denominator range -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

noncomputable def smallMajorArcModel (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ)
    (F W : ℝ → ℂ) (a : ℕ+ → ℂ) : ℂ :=
  (1/(j : ℂ))*∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
    ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*
      ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
        F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ
    else 0 else 0

theorem smallArcSum_fourierModel (B j : ℕ) [NeZero j] {X : ℝ} (hX : 0 < X)
    (Q : ℕ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) :
    smallArcSum B j X Q (fun q h x => F x*((X : ℂ)*a q*
      W ((j : ℝ)*X*(x-(h.val : ℝ)/(j*(q : ℕ) : ℕ))))) =
      smallMajorArcModel B j X Q F W a := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  unfold smallArcSum smallMajorArcModel
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  split_ifs with hq
  · rw [mul_sum]
    apply sum_congr rfl
    intro h _
    split_ifs
    · dsimp only
      have hc := local_arc_change_variables hjR hX.ne'
        ((h.val : ℝ)/(j*(q : ℕ) : ℕ)) ((B : ℝ)^13)
        (fun x => F x*((X : ℂ)*a q*W ((j : ℝ)*X*(x-(h.val : ℝ)/(j*(q : ℕ) : ℕ)))))
      have he (ξ : ℝ) : (j : ℝ)*X*
          ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X)-
            (h.val : ℝ)/(j*(q : ℕ) : ℕ)) = ξ := by field_simp; ring
      simp_rw [he] at hc
      have hm : (fun ξ : ℝ => F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*
          ((X : ℂ)*a q*W ξ)) = fun ξ => ((X : ℂ)*a q)*
            (F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ) := by
        funext ξ
        ring
      rw [hm,intervalIntegral.integral_const_mul] at hc
      push_cast at hc ⊢
      have hs := congrArg (fun z : ℂ => (X : ℂ)⁻¹*z) hc
      simp only [← mul_assoc,inv_mul_cancel₀ hXC,one_mul] at hs
      have hz : (X : ℂ)⁻¹*(j : ℂ)*X = j := by field_simp
      rw [hz] at hs
      simp only [mul_assoc] at hs ⊢
      rw [one_div,hs,inv_mul_cancel_left₀ hjC]
    · simp
  · simp

theorem smallMajorArc_energy_approximation :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ F G H W : ℝ → ℂ, Continuous F → Continuous G → Continuous H → Continuous W →
      Periodic F 1 → Periodic G 1 → Periodic (fun x => F x*G x*H x) 1 →
      ∀ a : ℕ+ → ℂ, ∀ E : ℝ, 0 ≤ E →
      (∀ q ∈ positiveDenominators (B^12), (q : ℕ) ≤ Q →
        ∀ h : ZMod (j*(q : ℕ)), h.val.Coprime (q : ℕ) →
        ∀ ξ : ℝ, |ξ| ≤ (B : ℝ)^13 →
        ‖H ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))-(X : ℂ)*a q*W ξ‖ ≤ E) →
      ‖(∫ x in smallMajorArcRegion B j X Q, F x*G x*H x)-
        smallMajorArcModel B j X Q (fun x => F x*G x) W a‖ ≤
        E/2*((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2)) := by
  filter_upwards [smallArcSum_error_bound] with B hB
  intro X hX hlog j hj Q F G H W hF hG hH hW hpF hpG hp a E hE he
  let : NeZero j := hj
  have hjX : 0 < (j : ℝ)*X := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne j)) hX
  have hh := hB X hX hlog j hj Q F G H hF hG hH hpF hpG hp
    (fun q h x => (X : ℂ)*a q*W ((j : ℝ)*X*(x-(h.val : ℝ)/(j*(q : ℕ) : ℕ))))
    (fun q h => continuous_const.mul (hW.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))) E hE (by
      intro q hq hqQ h hcop x hx
      let ξ := (j : ℝ)*X*(x-(h.val : ℝ)/(j*(q : ℕ) : ℕ))
      have hξ : |ξ| ≤ (B : ℝ)^13 := by
        apply abs_le.mpr
        constructor
        · dsimp [ξ]
          have ht := mul_le_mul_of_nonneg_left hx.1 hjX.le
          have hc : (j : ℝ)*X*((B : ℝ)^13/(j*X)) = (B : ℝ)^13 :=
            mul_div_cancel₀ _ hjX.ne'
          nlinarith
        · dsimp [ξ]
          have ht := mul_le_mul_of_nonneg_left hx.2 hjX.le
          have hc : (j : ℝ)*X*((B : ℝ)^13/(j*X)) = (B : ℝ)^13 :=
            mul_div_cancel₀ _ hjX.ne'
          nlinarith
      have hxξ : (h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X) = x := by
        dsimp [ξ]
        rw [mul_div_cancel_left₀ _ hjX.ne']
        ring
      simpa only [hxξ] using he q hq hqQ h hcop ξ hξ)
  rw [smallArcSum_fourierModel B j hX Q (fun x => F x*G x) W a] at hh
  exact hh

end JointDickman

end OAI
