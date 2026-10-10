import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSliceMoments
import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows

namespace OAI

/-! The literal divisor rows in the coprimality expansion are the
shortened coefficient sums. Only harmless unit phases and a character
of modulus at most one are removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSliceRow_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 0 (u+2*Real.pi*t)‖ := by
  rw [fullPrime_divisor_sum_eq_slice W X hX hlo hhi hf]
  have hfp := norm_pos_of_ne_zero (primary_ne_zero hf)
  have he : (∑ n ∈ fullPrimeSliceSupport R W X f e,
      star (fullPrimeCoefficient R W X (f*n)*mellinPhase u (norm (f*n)))*
        star (gramMellinPhase t (norm (f*n)/N))*star (cubicSymbol (f*n) h)) =
      star ((mellinPhase (u+2*Real.pi*t) (norm f)*
        mellinPhase (-(2*Real.pi*t)) N*cubicSymbol f h)*
        fullPrimeSliceSum R W X f e h 1 0 (u+2*Real.pi*t)) := by
    rw [fullPrimeSliceSum,Finset.mul_sum,star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp := (fullPrimeSliceSupport_bounds R W X f e hn).1
    have hnpos := norm_pos_of_ne_zero (primary_ne_zero hnp)
    rw [norm_mul_eq,gramMellinPhase_ratio t (mul_pos hfp hnpos) hN,
      mellinPhase_mul_pos u hfp hnpos,mellinPhase_mul_pos (2*Real.pi*t) hfp hnpos,
      cubicSymbol_mul_lower (primary_ne_zero hf) (primary_ne_zero hnp)]
    simp only [theta_zero,one_mul,mul_one,mellinPhase_add_height,star_mul]
    ring
  rw [he,norm_star,norm_mul,norm_mul,norm_mul,mellinPhase_norm,
    mellinPhase_norm,one_mul,one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hf h)

lemma fullPrimeSliceRow_reverse_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 0 (u-2*Real.pi*t)‖ := by
  have he := fullPrimeSliceRow_norm_le W X hX hlo hhi hf e h u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  congr 2
  ring

end CubicFirstMoment

end

end OAI
