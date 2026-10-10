import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.CubeModelOverlap
import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! Restoring all pairs in the cube model costs an arbitrary logarithmic
power on the actual rough prime convolution. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_cube_model_overlap_log_saving {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u : ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∀ i, (L r)^c < X i) → 0 ≤ A →
      ‖cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (negative_power_log_saving hc (a+k))
  let C := 2*R^Fintype.card ι*(Fintype.card ι:ℝ)*E*‖cubeProfileIntegral V‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,T₀,by positivity,?_⟩
  intro r X A e u hT₀ hL hX hprod hrough hA
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hN (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) : L r ≤ norm b := by
    simpa only [hprod] using
      (fullPrimeProduct_norm_bounds R (W r) X (fun i => zero_lt_one.trans_le (hX i))
        (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).1
  have hb := cube_model_coprimality_error _ (angularHeightPrimeCoefficient ℓ R (W r) X) u V hA hLp hN
  have ho := fullPrime_overlap_energy hR (Real.rpow_pos_of_pos hLp c) hLp (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) hprod (hlo r) (hhi r) hrough e
  have hnorm (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) :=
    angularHeightPrimeCoefficient_norm ℓ R (W r) X
      (fullSquarefreePrimeSupport_primary R (W r) X e hb).1
  have ho' : (∑ a ∈ fullSquarefreePrimeSupport R (W r) X e,
      ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        if ¬IsCoprime a b then ‖angularHeightPrimeCoefficient ℓ R (W r) X a‖*
          ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖ else 0) ≤
      (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L r/(L r)^c)*
        ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e, ‖fullPrimeCoefficient R (W r) X b‖^2 := by
    convert ho using 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hnorm a ha, hnorm b hb]
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤ E*L r*(1+Real.log (L r))^a :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans
      (henergy r X hL hX hprod)
  have hlog : (1+Real.log (L r))^a*(L r)^(-c) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hLp]
    norm_num
  have hfactor :
      (A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        ((18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L r/(L r)^c)*
          (E*L r*(1+Real.log (L r))^a)) =
      C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*((1+Real.log (L r))^a*(L r)^(-c)) := by
    rw [← hpower]
    simp only [Real.rpow_neg hLp.le]
    dsimp [C]
    field_simp
    ring
  apply (hb.trans (mul_le_mul_of_nonneg_left
    (ho'.trans (mul_le_mul_of_nonneg_left he (by positivity))) (by positivity))).trans
  rw [hfactor]
  calc
    _ ≤ C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*(1/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ (C+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
