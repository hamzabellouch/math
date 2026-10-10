import OAI.NumberTheory.CubicMoment.Estimates.CubeErrorPowers
import OAI.NumberTheory.CubicMoment.Estimates.PrimeCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.LogPoissonEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The literal cube term has its model with arbitrary logarithmic
saving once H=L²/A is a sufficiently large log-power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cube_poisson_log_saving {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c < X i) →
      0 < A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      ‖cubePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A-
        coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨C,D,hC,hD,hbound⟩ := cubePoissonContribution_uniform_error V hV hV'
  obtain ⟨E,a,hE,henergy⟩ := logarithmic_full_l1_square hR hW hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (negative_power_log_saving hc (a+k))
  let K := C*E/27+2*(Fintype.card ι:ℝ)*D*E/9+1
  refine ⟨3*(a+k),K,T₀,by dsimp [K]; positivity,?_⟩
  intro r X A e u hT₀ hL hX hprod hrough hA hcut
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz₁ : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz₁
  have hAL : A ≤ (L r)^2 := hcut.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz₁))
  have hS : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e, primary b ∧ Squarefree b :=
    fun b hb => fullSquarefreePrimeSupport_primary R (W r) X e hb
  have hN : ∀ b ∈ fullSquarefreePrimeSupport R (W r) X e, L r ≤ norm b := by
    intro b hb
    have hn := (fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).1
    simpa only [hprod] using hn
  have hp (a b : Eisenstein)
      (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e)
      (hb : b ∈ fullSquarefreePrimeSupport R (W r) X e) :=
    fullPrime_pair_reciprocal_sum_le (Real.rpow_pos_of_pos hLp c)
      (W r) X (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) hrough e ha hb
  have hb := hbound _ hS A (L r) (2*(Fintype.card ι:ℝ)/(L r)^c) hA hLp (by positivity)
    (hAL.trans (by nlinarith [sq_nonneg (L r)])) hN (fun a ha b hb => hp a b ha hb)
    (fullPrimeCoefficient R (W r) X) u
  have he := henergy r X hL hX hprod e
  have hlattice := cube_lattice_error_scale hA hLp hz a k hcut
  have hlog : (1+Real.log (L r))^a*(L r)^(-c) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  have hpower : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
    rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hLp]
    norm_num
  have hfactor : (C*A/(27*L r)+D*A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*
      (2*(Fintype.card ι:ℝ)/(L r)^c)/9)*(E*(L r)^2*(1+Real.log (L r))^a) =
      (C*E/27)*(A*L r*(1+Real.log (L r))^a)+
      (2*(Fintype.card ι:ℝ)*D*E/9)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
        ((1+Real.log (L r))^a*(L r)^(-c)) := by
    rw [← hpower]
    simp only [Real.rpow_neg hLp.le]
    field_simp
  apply (hb.trans (mul_le_mul_of_nonneg_left he (by positivity))).trans
  rw [hfactor]
  calc
    _ ≤ (C*E/27)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)+
        (2*(Fintype.card ι:ℝ)*D*E/9)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*
          (1/(1+Real.log (L r))^k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hlattice (by positivity))
        (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ = (C*E/27+2*(Fintype.card ι:ℝ)*D*E/9)*
        (A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ K*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [K]
      linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
