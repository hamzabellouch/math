import OAI.NumberTheory.CubicMoment.Estimates.LargeDivisorMass
import OAI.NumberTheory.CubicMoment.Estimates.LargeDivisorExponents
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment
import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy

namespace OAI

/-! Large common prime divisors have an arbitrary logarithmic saving
for the actual full prime-convolution mass. The bound follows from the outer sieve, shortened
energy sum, and elementary power gap. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_large_divisor_log_saving {R δ : ℝ} (hR : 1 ≤ R)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (e : Eisenstein) (H U : Finset Eisenstein) (u t N₀ : ℝ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      1 ≤ B → B ≤ (L r)^(1+δ/4) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ p ∈ U, primaryPrime p) → 0 < N₀ →
      (∑ s ∈ U.powerset.filter (fun s => (L r)^δ < norm (∏ p ∈ s, p)),
        fullPrimeDivisorMellinMass R (W r) X e H u N₀ (∏ p ∈ s, p) t) ≤
      K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,hC,hbound⟩ := fullPrime_large_divisor_mass (ι := ι)
    (show 0 < δ/100 by positivity)
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  let A := R^Fintype.card ι
  let D := (2*A)^(δ/100)*(1+A^(2/3:ℝ)+A)
  have hA : 1 ≤ A := one_le_pow₀ hR
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp
    (negative_power_log_saving (show 0 < δ/20 by positivity) (a+k))
  refine ⟨C*(2^Fintype.card ι:ℝ)*(E+1)*D,T₀,by positivity,?_⟩
  intro r X B e H U u t N₀ hT₀ hL hX hprod hB hBL hH hU hN₀
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hDel : 1 ≤ (L r)^δ := Real.one_le_rpow hL hδ.le
  have hDL : (L r)^δ ≤ L r := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL hδ₁
  let N := A*L r/(L r)^δ
  have hNeq : N = A*(L r)^(1-δ) := by
    dsimp [N]
    rw [Real.rpow_sub hLp,Real.rpow_one]
    ring
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hm := hbound R (W r) X e H U u t N₀ B ((L r)^δ) hR
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) hU hN₀ hB hDel
    (by simpa only [hprod] using hDL) hH
  rw [hprod] at hm
  have he : (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
      ‖fullPrimeCoefficient R (W r) X b‖^2) ≤
      (E+1)*L r*(1+Real.log (L r))^a := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans
    apply (henergy r X hL hX hprod).trans
    nlinarith [mul_nonneg hLp.le (pow_nonneg hz.le a)]
  have hn := shortened_outer_power_saving hL (zero_lt_one.trans_le hB) hN hA hδ hδ₁
    (show δ/4 ≤ 1/4 by linarith) le_rfl hBL hNeq.le
  have hlog : (1+Real.log (L r))^a*(L r)^(-δ/20) ≤ 1/(1+Real.log (L r))^k := by
    rw [show -δ/20 = -(δ/20) by ring]
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ C*(2^Fintype.card ι:ℝ)*(2*B*N)^(δ/100)*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*((E+1)*L r*(1+Real.log (L r))^a) :=
      hm.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        ((2*B*N)^(δ/100)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*L r) := by ring
    _ ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*(1+Real.log (L r))^a)*
        (D*(L r)^2*B^(1/3:ℝ)*(L r)^(-δ/20)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ)*
        ((1+Real.log (L r))^a*(L r)^(-δ/20)) := by ring
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ (C*(2^Fintype.card ι:ℝ)*(E+1)*D)*(L r)^2*B^(1/3:ℝ) by positivity)

end CubicFirstMoment

end

end OAI
