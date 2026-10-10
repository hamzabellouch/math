import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.GramSliceRows

namespace OAI

/-! Literal angular prime coefficients and the two signed Mellin rows.
Only unit phases are removed; the angular index remains fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def angularHeightPrimeCoefficient (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (b : Eisenstein) : ℂ := fullPrimeCoefficient R W X b*theta ℓ b

lemma angularHeightPrimeCoefficient_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {b : Eisenstein} (hb : primary b) :
    ‖angularHeightPrimeCoefficient ℓ R W X b‖ = ‖fullPrimeCoefficient R W X b‖ := by
  rw [angularHeightPrimeCoefficient,norm_mul,norm_theta (primary_ne_zero hb),mul_one]

lemma angularHeightPrimeCoefficient_l1 (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖angularHeightPrimeCoefficient ℓ R W X b‖) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖ := by
  exact Finset.sum_congr rfl (fun b hb => angularHeightPrimeCoefficient_norm ℓ R W X
    (fullSquarefreePrimeSupport_primary R W X e hb).1)

lemma angularHeightPrimeCoefficient_energy (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖angularHeightPrimeCoefficient ℓ R W X b‖^2) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [angularHeightPrimeCoefficient_norm ℓ R W X
    (fullSquarefreePrimeSupport_primary R W X e hb).1]

lemma angularHeightPrimeCoefficient_sum_squarefree (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
      (fun b => IsCoprime b e), angularHeightPrimeCoefficient ℓ R W X b*f b) =
    ∑ b ∈ fullSquarefreePrimeSupport R W X e, angularHeightPrimeCoefficient ℓ R W X b*f b := by
  simpa only [angularHeightPrimeCoefficient,mul_assoc] using
    fullPrimeCoefficient_sum_squarefree R W X e (fun b => theta ℓ b*f b)

lemma angular_fullStructured_gram_twist
    (R : ℝ) (h e : Eisenstein) (u t : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {N : ℝ} (hN : 0 < N) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun b => IsCoprime b e),
      angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b)*cubicSymbol b h*
        gramMellinPhase t (norm b/N)) =
      mellinPhase (-(2*Real.pi*t)) N*fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X := by
  unfold fullStructuredAngularSum angularHeightPrimeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hbp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) (Finset.mem_filter.mp hb).1
  rw [gramMellinPhase_ratio t (norm_pos_of_ne_zero (primary_ne_zero hbp)) hN,
    mellinPhase_add_height]
  simp only [one_mul]
  ring

theorem angular_fullStructuredPrimeRow_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)‖ =
      ‖fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X‖ := by
  have he : (∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        star (gramMellinPhase t (norm b/N))*star (cubicSymbol b h)) =
      star (mellinPhase (-(2*Real.pi*t)) N*
        fullStructuredAngularSum R h 1 e ℓ (u+2*Real.pi*t) W X) := by
    calc
      _ = star (∑ b ∈ fullSquarefreePrimeSupport R W X e,
          angularHeightPrimeCoefficient ℓ R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [star_mul]
        ring
      _ = star (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
          (fun b => IsCoprime b e), angularHeightPrimeCoefficient ℓ R W X b*
            (mellinPhase u (norm b)*cubicSymbol b h*gramMellinPhase t (norm b/N))) :=
        congrArg star (angularHeightPrimeCoefficient_sum_squarefree ℓ R W X e _).symm
      _ = _ := by
        congr 1
        convert angular_fullStructured_gram_twist ℓ R h e u t W X hN using 1
        apply Finset.sum_congr rfl
        intro b hb
        ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

theorem angular_fullStructuredPrimeRow_reverse_norm (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ b ∈ fullSquarefreePrimeSupport R W X e,
      star (angularHeightPrimeCoefficient ℓ R W X b*mellinPhase u (norm b))*
        gramMellinPhase t (norm b/N)*star (cubicSymbol b h)‖ =
      ‖fullStructuredAngularSum R h 1 e ℓ (u-2*Real.pi*t) W X‖ := by
  have he := angular_fullStructuredPrimeRow_norm ℓ R W X h e u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  congr 2
  ring


lemma angular_fullPrimeSliceRow_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)‖ := by
  rw [fullPrime_divisor_sum_eq_slice W X hX hlo hhi hf]
  have hfp := norm_pos_of_ne_zero (primary_ne_zero hf)
  have he : (∑ n ∈ fullPrimeSliceSupport R W X f e,
      star (angularHeightPrimeCoefficient ℓ R W X (f*n)*mellinPhase u (norm (f*n)))*
        star (gramMellinPhase t (norm (f*n)/N))*star (cubicSymbol (f*n) h)) =
      star ((theta ℓ f*mellinPhase (u+2*Real.pi*t) (norm f)*
        mellinPhase (-(2*Real.pi*t)) N*cubicSymbol f h)*
        fullPrimeSliceSum R W X f e h 1 ℓ (u+2*Real.pi*t)) := by
    rw [fullPrimeSliceSum,Finset.mul_sum,star_sum]
    simp only [angularHeightPrimeCoefficient]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp := (fullPrimeSliceSupport_bounds R W X f e hn).1
    have hnpos := norm_pos_of_ne_zero (primary_ne_zero hnp)
    rw [theta_mul, norm_mul_eq,gramMellinPhase_ratio t (mul_pos hfp hnpos) hN,
      mellinPhase_mul_pos u hfp hnpos,mellinPhase_mul_pos (2*Real.pi*t) hfp hnpos,
      cubicSymbol_mul_lower (primary_ne_zero hf) (primary_ne_zero hnp)]
    simp only [one_mul,mellinPhase_add_height,star_mul]
    ring
  rw [he,norm_star,norm_mul,norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hf),mellinPhase_norm,
    mellinPhase_norm,one_mul,one_mul]
  simp only [one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hf h)

lemma angular_fullPrimeSliceRow_reverse_norm_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e h : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖ ≤
    ‖fullPrimeSliceSum R W X f e h 1 ℓ (u-2*Real.pi*t)‖ := by
  have he := angular_fullPrimeSliceRow_norm_le ℓ W X hX hlo hhi hf e h u (-t) hN
  simp only [gramMellinPhase_neg,star_star] at he
  convert he using 1
  congr 2
  ring

end CubicFirstMoment

end

end OAI
