import OAI.NumberTheory.CubicMoment.Estimates.MellinEnvelopeBound
import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeNormRange

namespace OAI

/-! A polynomial coarse envelope for the unchanged full prime rows,
uniform in Mellin height and the ambient set of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSupport_card_bound {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤ 18*(R^Fintype.card ι*(∏ i, X i)) := by
  apply primary_support_card_le _ (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le)))
  intro b hb
  exact ⟨(fullSquarefreePrimeSupport_primary R W X e hb).1,
    (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2⟩

lemma fullPrimeCoefficient_l1_square {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖)^2 ≤
      18*(R^Fintype.card ι*(∏ i, X i))*
        ∑ b ∈ orderedConvolutionSupport (fullPrimeSupport R W X), ‖fullPrimeCoefficient R W X b‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (fullSquarefreePrimeSupport R W X e)
    (fun _ => (1:ℝ)) (fun b => ‖fullPrimeCoefficient R W X b‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  apply hcs.trans
  apply mul_le_mul (fullPrimeSupport_card_bound hR W X hX hlo hhi e)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le))))

theorem logarithmic_full_mellin_envelope {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → ∀ (e : Eisenstein) (H U : Finset Eisenstein),
      (∀ p ∈ U, primaryPrime p) → ∀ u : ℝ,
      let v := fun b => star (fullPrimeCoefficient R (W r) X b*mellinPhase u (norm b))
      coprimeMellinEnvelope (fullSquarefreePrimeSupport R (W r) X e) H U v v ≤
        K*(H.card:ℝ)*(L r)^2*(1+Real.log (L r))^A := by
  obtain ⟨C,A,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨(2^Fintype.card ι:ℝ)*18*R^Fintype.card ι*C,A,by positivity,?_⟩
  intro r X hL hX hprod e H U hU u
  dsimp only
  have hb := fullPrime_coprimeMellinEnvelope R (W r) X e H U hU
    (fun b => star (fullPrimeCoefficient R (W r) X b*mellinPhase u (norm b)))
    (fun b => star (fullPrimeCoefficient R (W r) X b*mellinPhase u (norm b)))
  simp only [norm_star,norm_mul,mellinPhase_norm,mul_one] at hb
  have hl := fullPrimeCoefficient_l1_square (zero_le_one.trans hR) (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) e
  rw [hprod] at hl
  have he := henergy r X hL hX hprod
  have hl' := hl.trans (mul_le_mul_of_nonneg_left he (by positivity))
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hl' (mul_nonneg (Nat.cast_nonneg H.card) (by positivity : 0 ≤ (2^Fintype.card ι:ℝ)))
  convert hm using 1 <;> ring

end CubicFirstMoment

end

end OAI
