import OAI.NumberTheory.CubicMoment.Estimates.DispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.SievedDispersion
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeOverlapEnergy

namespace OAI

/-! The literal model polynomial has the expected energy bound on a
norm annulus. This retains the logarithmic coefficient complexity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_logarithmic_dispersionModel_energy {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ r X e u,
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ‖dispersionModel (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u‖^2 ≤
        K*(L r)^(5/3:ℝ)*(1+Real.log (L r))^a := by
  obtain ⟨C,a,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨18*R^Fintype.card ι*C,a,by positivity,?_⟩
  intro r X e u hL hX hprod
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  let S := fullSquarefreePrimeSupport R (W r) X e
  have hnorm (b : Eisenstein) (hb : b ∈ S) :
      L r ≤ norm b ∧ norm b ≤ R^Fintype.card ι*L r := by
    simpa only [hprod] using fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1
  have hcard : (S.card:ℝ) ≤ 18*(R^Fintype.card ι*L r) := by
    have hsub : S ⊆ nonzeroNormBall (R^Fintype.card ι*L r) := by
      intro b hb
      exact mem_nonzeroNormBall.mpr
        ⟨(hnorm b hb).2,primary_ne_zero (fullSquarefreePrimeSupport_primary R (W r) X e hb).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le (by positivity))
  have he : (∑ b ∈ S, ‖angularHeightPrimeCoefficient ℓ R (W r) X b‖^2) ≤
      C*L r*(1+Real.log (L r))^a := by
    rw [show S = fullSquarefreePrimeSupport R (W r) X e from rfl, angularHeightPrimeCoefficient_energy]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (henergy r X hL hX hprod)
  apply (dispersionModel_norm_sq_le S _ u hLp (fun b hb => (hnorm b hb).1)).trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_right hcard (by positivity)) he
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)).trans_eq
  have hp : L r*(L r)^(-(1/3:ℝ))*L r = (L r)^(5/3:ℝ) := by
    calc
      _ = (L r)^(1:ℝ)*(L r)^(-(1/3:ℝ))*(L r)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hLp,←Real.rpow_add hLp]; norm_num
  calc
    _ = (18*R^Fintype.card ι*C)*(L r*(L r)^(-(1/3:ℝ))*L r)*(1+Real.log (L r))^a := by ring
    _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
