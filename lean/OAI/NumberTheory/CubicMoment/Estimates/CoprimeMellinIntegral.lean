import OAI.NumberTheory.CubicMoment.Estimates.CoprimeMellinMass

namespace OAI

/-! An integral estimate for the literal radial Poisson form in terms of
the actual divisor-restricted character moments. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellin_character_row_norm_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (h : Eisenstein) (t : ℝ) :
    ‖∑ a ∈ S, v a*gramMellinPhase t (y a)*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ S, ‖v a‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul,norm_mul,norm_gramMellinPhase,mul_one,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) _)

lemma coprimeMellinMass_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : 0 ≤ coprimeMellinMass S H U v w y t := by
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)

lemma coprimeMellinMass_continuous (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) : Continuous (coprimeMellinMass S H U v w y) := by
  unfold coprimeMellinMass
  apply continuous_finsetSum
  intro s hs
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _).star).mul continuous_const
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const

lemma coprimeMellinMass_le_envelope (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeMellinMass S H U v w y t ≤
      ∑ s ∈ U.powerset, (H.card:ℝ)*
        ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2+
         (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)/2 := by
  unfold coprimeMellinMass
  apply Finset.sum_le_sum
  intro s hs
  let F := S.filter (fun a => (∏ p ∈ s, p) ∣ a)
  have hF : ∀ a ∈ F, primary a := fun a ha => hS a (Finset.mem_filter.mp ha).1
  have hneg (h : Eisenstein) :
      ‖∑ a ∈ F, v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ F, ‖v a‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_mul,norm_mul,norm_star,norm_gramMellinPhase,mul_one,norm_star]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hF a ha) _)
  have hv := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (hneg h) 2)
  have hw := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (mellin_character_row_norm_le F hF w y h t) 2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hv hw
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (add_le_add hv hw).trans_eq (by dsimp [F]; ring)

theorem coprimeRadialForm_norm_le_mass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, x h ∈ Icc (1:ℝ) 2)
    (hy : ∀ a ∈ S, y a ∈ Icc (1:ℝ) (Real.sqrt 2))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖coprimeRadialForm S H v w phase x y W ρ‖ ≤
      ∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖*
        coprimeMellinMass S H U v w y t := by
  have hc := gramMellinCoefficient_integrable W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase x y).aestronglyMeasurable
    (Eventually.of_forall (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase hphase x y))
  have hm := hc.norm.mul_bdd
    (coprimeMellinMass_continuous S H U v w y).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (coprimeMellinMass_nonneg S H U v w y t)]
      exact coprimeMellinMass_le_envelope S H U (fun a ha => (hS a ha).1) v w y t))
  rw [coprimeRadialForm_mellin S H v w phase x y hx hy W hW hW' hρ]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hi.norm hm
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_coprimeMellinKernel_le_mass S H U hS hU hSU v w phase hphase x y t)
    (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
