import OAI.NumberTheory.CubicMoment.Estimates.DispersionModelEnergy

namespace OAI

/-! Absolute model mass controls both the model and the coprimality error
in its Type-I replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def dispersionAbsoluteModel (S : Finset Eisenstein) (β : Eisenstein → ℂ) : ℝ :=
  ∑ b ∈ S, ‖β b‖*norm b^(-1/6:ℝ)

lemma dispersionAbsoluteModel_nonneg (S : Finset Eisenstein) (β : Eisenstein → ℂ) :
    0 ≤ dispersionAbsoluteModel S β :=
  Finset.sum_nonneg (fun b _ => mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (norm_nonneg b) _))

lemma norm_dispersionModel_le_absolute (S : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) :
    ‖dispersionModel S β u‖ ≤ dispersionAbsoluteModel S β := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  simp only [norm_mul,norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg b) _),le_refl]

lemma dispersionAbsoluteModel_sq_le (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {L : ℝ} (hL : 0 < L) (hS : ∀ b ∈ S, L ≤ norm b) :
    (dispersionAbsoluteModel S β)^2 ≤
      (S.card:ℝ)*L^(-(1/3:ℝ))*(∑ b ∈ S, ‖β b‖^2) := by
  have he : dispersionModel S (fun b => (‖β b‖:ℂ)) 0 = (dispersionAbsoluteModel S β:ℂ) := by
    unfold dispersionModel dispersionAbsoluteModel
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [normTwist,zero_mul,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,
      Complex.ofReal_mul]
  have hh := dispersionModel_norm_sq_le S (fun b => (‖β b‖:ℂ)) 0 hL hS
  simpa only [he,Complex.norm_real,Real.norm_eq_abs,sq_abs,abs_norm] using hh

theorem logarithmic_dispersionAbsoluteModel_energy {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ r X e,
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (dispersionAbsoluteModel (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X))^2 ≤
        K*(L r)^(5/3:ℝ)*(1+Real.log (L r))^a := by
  obtain ⟨C,a,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨18*R^Fintype.card ι*C,a,by positivity,?_⟩
  intro r X e hL hX hprod
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
  have he : (∑ b ∈ S, ‖fullPrimeCoefficient R (W r) X b‖^2) ≤
      C*L r*(1+Real.log (L r))^a :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (henergy r X hL hX hprod)
  apply (dispersionAbsoluteModel_sq_le S _ hLp (fun b hb => (hnorm b hb).1)).trans
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
