import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale
import OAI.NumberTheory.CubicMoment.Estimates.DispersionModelEnergy

namespace OAI

/-! The factored squarefree model and μ²(ab) differ by a negligible
shared-prime sum for the actual independent rough-prime convolution. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_prime_model_overlap_log_saving {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R Q c M : ℝ} (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hc : 0 < c) (hM : 0 ≤ M)
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (k d : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ r X e u A (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∀ i, (L r)^c < X i) → 0 < A →
      (∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ Q*A) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      ‖modelOverlap P (fullSquarefreePrimeSupport R (W r) X e)
        α (fullPrimeCoefficient R (W r) X) u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨Cβ,a,hCβ,hβ⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (overlap_power_log_saving hc (d+a) k)
  let Cb := 18*R^Fintype.card ι
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  let K₀ := cStar^2*Cb*(Fintype.card ι:ℝ)*18*Q*Cβ*M
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀,Cb]; positivity
  refine ⟨Real.sqrt K₀+1,T₀,by positivity,?_⟩
  intro r X e u A P α hT₀ hL hX hprod hrough hA hP hα
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := fullPrimeCoefficient R (W r) X
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hD : 0 < (L r)^c := Real.rpow_pos_of_pos hLp _
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ L r ≤ norm b := by
    intro b hb
    exact ⟨(fullSquarefreePrimeSupport_primary R (W r) X e hb).1,
      (fullSquarefreePrimeSupport_primary R (W r) X e hb).2,
      by simpa only [hprod] using (fullPrimeProduct_norm_bounds R (W r) X
        (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).1⟩
  have hcard : (S.card:ℝ) ≤ Cb*L r := by
    have hsub : S ⊆ nonzeroNormBall (R^Fintype.card ι*L r) := by
      intro b hb
      refine mem_nonzeroNormBall.mpr ⟨?_,primary_ne_zero (hS b hb).1⟩
      simpa only [hprod] using (fullPrimeProduct_norm_bounds R (W r) X
        (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp hb).1).2
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((nonzeroNormBall_card_le (by positivity)).trans_eq (by dsimp [Cb]; ring))
  have henergy : (∑ b ∈ S, ‖β b‖^2) ≤ Cβ*L r*(1+Real.log (L r))^a :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (hβ r X hL hX hprod)
  have hn : ∀ b ∈ S, (primaryPrimeFactors b).card ≤ Fintype.card ι := fun b hb =>
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R (W r) X) (Finset.mem_filter.mp hb).1
  have hpn : ∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, (L r)^c ≤ norm p := by
    intro b hb p hpb
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R (W r) X
      (primaryPrimeFactor_spec (hS b hb).1 hpb).1
      (primaryPrimeFactor_spec (hS b hb).1 hpb).2 (Finset.mem_filter.mp hb).1
    have hw := ((fullPrimeSupport_mem_iff (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hhi r) i p).mp hi).2
    have hr : 1 ≤ norm p/X i := le_of_not_gt (fun hh => hw (hlo r i _ hh))
    exact (hrough i).le.trans (by simpa using
      (le_div_iff₀ (zero_lt_one.trans_le (hX i))).mp hr)
  have hraw := modelOverlap_norm_sq_le P S α β u hA hLp (mul_nonneg hQ hA.le) hD
    (fun b hb => ⟨primary_ne_zero (hP b hb).1,(hP b hb).2⟩) hS (Fintype.card ι) hn hpn
  have hsq : ‖modelOverlap P S α β u‖^2 ≤
      K₀*A^(5/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^(2*k) := by
    calc
      _ ≤ (cStar*A^(-1/6:ℝ)*(L r)^(-1/6:ℝ))^2*
          ((Cb*L r*(M*A*(1+Real.log (L r))^d))*
            ((Fintype.card ι:ℝ)*(18*(Q*A)/(L r)^c)*(Cβ*L r*(1+Real.log (L r))^a))) := by
        apply hraw.trans
        gcongr
      _ = K₀*A^(5/3:ℝ)*(L r)^(5/3:ℝ)*
          ((1+Real.log (L r))^(d+a)/(L r)^c) := by
        rw [model_overlap_scale hA hLp]
        dsimp [K₀]
        ring
      _ ≤ K₀*A^(5/3:ℝ)*(L r)^(5/3:ℝ)*(1/(1+Real.log (L r))^(2*k)) :=
        mul_le_mul_of_nonneg_left (hT (L r) hT₀) (by positivity)
      _ = _ := by ring
  apply (norm_le_bilinear_of_square hK₀ hA hLp hz k hsq).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Real.sqrt K₀ ≤ Real.sqrt K₀+1)
        (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hLp.le _)) (pow_nonneg hz.le _)

end CubicFirstMoment

end

end OAI
