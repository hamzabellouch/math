import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightKernel

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

lemma norm_square_twisted_sum (B : Finset Eisenstein) (c : Eisenstein → ℂ) (u : ℝ) :
    ((‖∑ b ∈ B, c b*normTwist u b‖^2:ℝ):ℂ) =
      ∑ b ∈ B, ∑ d ∈ B, (c b*star (c d))*(normTwist u b*star (normTwist u d)) := by
  have he := Complex.mul_conj' (∑ b ∈ B, c b*normTwist u b)
  simp only [starRingEnd_apply] at he
  rw [Complex.ofReal_pow,←he]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma averaged_finite_mean_square (B : Finset Eisenstein) (c : Eisenstein → ℂ) (u T : ℝ) :
    (T:ℂ)⁻¹*(∫ t in T..2*T, ((‖∑ b ∈ B, c b*normTwist (u+t) b‖^2:ℝ):ℂ)) =
      ∑ b ∈ B, ∑ d ∈ B, (c b*star (c d))*
        (normTwist u b*star (normTwist u d))*
        mellinHeightKernel T (Real.log (norm b)-Real.log (norm d)) := by
  have hc (b d : Eisenstein) : Continuous
      (fun t : ℝ => (c b*star (c d))*(normTwist (u+t) b*star (normTwist (u+t) d))) := by
    exact continuous_const.mul (((continuous_normTwist b).comp (continuous_const.add continuous_id)).mul
      (((continuous_normTwist d).comp (continuous_const.add continuous_id)).star))
  have hi (b d : Eisenstein) : IntervalIntegrable
      (fun t : ℝ => (c b*star (c d))*(normTwist (u+t) b*star (normTwist (u+t) d)))
      volume T (2*T) := (hc b d).intervalIntegrable T (2*T)
  have hrow (b : Eisenstein) : IntervalIntegrable
      (fun t : ℝ => ∑ d ∈ B, (c b*star (c d))*(normTwist (u+t) b*star (normTwist (u+t) d)))
      volume T (2*T) := (continuous_finsetSum B (fun d _ => hc b d)).intervalIntegrable T (2*T)
  simp_rw [norm_square_twisted_sum]
  rw [intervalIntegral.integral_finsetSum (fun b _ => hrow b)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [intervalIntegral.integral_finsetSum (fun d _ => hi b d)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [intervalIntegral.integral_const_mul]
  calc
    _ = (c b*star (c d))*((T:ℂ)⁻¹*
        ∫ t in T..2*T, normTwist (u+t) b*star (normTwist (u+t) d)) := by ring
    _ = _ := by rw [averaged_normTwist_correlation]; ring

/-- The zero spectral difference contributes the exact coefficient
square, even when different elements have the same norm. -/
lemma height_diagonal_coefficient (c : ℂ) {T : ℝ} (hT : T ≠ 0) (u : ℝ) (b : Eisenstein) :
    (c*star c)*(normTwist u b*star (normTwist u b))*
      mellinHeightKernel T (Real.log (norm b)-Real.log (norm b)) = ((‖c‖^2:ℝ):ℂ) := by
  rw [sub_self,mellinHeightKernel_zero hT,mul_one]
  have hb := Complex.mul_conj' (normTwist u b)
  have hc := Complex.mul_conj' c
  simp only [starRingEnd_apply] at hb hc
  rw [hb,hc,norm_normTwist]
  norm_num

lemma averaged_finite_mean_square_diagonal (B : Finset Eisenstein)
    (c : Eisenstein → ℂ) (u : ℝ) {T : ℝ} (hT : T ≠ 0) :
    (T:ℂ)⁻¹*(∫ t in T..2*T, ((‖∑ b ∈ B, c b*normTwist (u+t) b‖^2:ℝ):ℂ)) =
      (∑ b ∈ B, ((‖c b‖^2:ℝ):ℂ))+
      ∑ b ∈ B, ∑ d ∈ B.erase b, (c b*star (c d))*
        (normTwist u b*star (normTwist u d))*
        mellinHeightKernel T (Real.log (norm b)-Real.log (norm d)) := by
  rw [averaged_finite_mean_square,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←Finset.add_sum_erase B _ hb,height_diagonal_coefficient (c b) hT u b]

end CubicFirstMoment

end

end OAI
