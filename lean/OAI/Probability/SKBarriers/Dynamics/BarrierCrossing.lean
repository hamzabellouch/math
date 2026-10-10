import Mathlib
import OAI.Probability.SKBarriers.Dynamics.TVSignBridge
import OAI.Probability.SKBarriers.Dynamics.KernelEvents

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem signEvent_le_stripOccupation {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (k : ℕ) (x : Config n) (hx : a₁ < overlap v x) :
    kernelEvent β J (fun y => overlap v y ≤ 0) k x ≤
      occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x := by
  have ha₁ : 0 < a₁ := by
    have : 0 < (2:ℝ)/(n:ℝ) := by positivity
    linarith
  induction k generalizing x with
  | zero =>
    rw [kernelEvent_zero,ite_eq_right (by linarith : ¬overlap v x ≤ 0)]
    exact occupation_nonneg _ _ _ _ _
  | succ k ih =>
    rw [kernelEvent_succ,occupation_recursion]
    have HH : (∑ z : Config n, heatBath β J x z*kernelEvent β J (fun y => overlap v y ≤ 0) k z) ≤
        ∑ z : Config n, heatBath β J x z*occupation β J
          (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hlow : overlap v z < a₀
      · have hz : heatBath β J x z = 0 := by
          by_contra hne
          have hp := lt_of_le_of_ne (heatBath_nonneg β J x z) (Ne.symm hne)
          have hs := heatBath_overlap_step hn β J v x z hp
          have hs' := neg_le_abs (overlap v z-overlap v x)
          linarith
        simp only [hz,zero_mul,le_refl]
      · by_cases hhigh : a₁ < overlap v z
        · exact mul_le_mul_of_nonneg_left (ih z hhigh) (heatBath_nonneg β J x z)
        · have hz : a₀ ≤ overlap v z ∧ overlap v z ≤ a₁ := ⟨le_of_not_gt hlow,le_of_not_gt hhigh⟩
          exact mul_le_mul_of_nonneg_left ((kernelEvent_le_one hn β J _ k z).trans
            (one_le_occupation β J _ k z hz)) (heatBath_nonneg β J x z)
    exact HH.trans (le_add_of_nonneg_left (kernelEvent_nonneg _ _ _ _ _))

theorem quarter_le_stripOccupation_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (k : ℕ) (x : Config n) (hx : a₁ < overlap v x)
    (hTV : discreteDistance β J x k ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x :=
  (discrete_sign_mass_of_tv hn β J x v k hTV).trans
    (signEvent_le_stripOccupation hn β J v ha₀ hgap k x hx)

theorem mass_mixed_high_le_strip {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀) (k : ℕ) :
    (∑ x : Config n, if a₁ < overlap v x ∧ discreteDistance β J x k ≤ (1/4:ℝ)
      then gibbs β J x else 0) ≤ 4*((k+1:ℕ):ℝ)*
        (∑ y : Config n, if a₀ ≤ overlap v y ∧ overlap v y ≤ a₁ then gibbs β J y else 0) := by
  have HH := Finset.sum_le_sum (s := (Finset.univ : Finset (Config n)))
    (f := fun x => if a₁ < overlap v x ∧ discreteDistance β J x k ≤ (1/4:ℝ) then gibbs β J x else 0)
    (g := fun x => 4*(gibbs β J x*occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x))
    (fun x _ => show _ ≤ _ from by
      split_ifs with hx
      · have H := quarter_le_stripOccupation_of_tv hn β J v ha₀ hgap k x hx.1 hx.2
        nlinarith [mul_le_mul_of_nonneg_left H (le_of_lt (gibbs_pos β J x))]
      · exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (gibbs_pos β J x))
          (occupation_nonneg _ _ _ _ _)))
  rw [← Finset.mul_sum,occupation_stationary hn] at HH
  simpa only [mul_assoc] using HH

end SK.Analytic

end
end

end

end OAI
