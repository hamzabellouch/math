import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionAbsoluteModel
import OAI.NumberTheory.CubicMoment.Estimates.MixedModelCoprime
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! After multiplication by the correction polynomial, restoring
mutual coprimality in the literal mixed model saves every log power. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_mixed_model_coprimality_log_saving {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c)
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 0)
    (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ r X e u A,
      T₀ ≤ L r → 1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (∀ i, (L r)^c < X i) → 0 < A →
      let S := fullSquarefreePrimeSupport R (W r) X e
      let β := angularHeightPrimeCoefficient ℓ R (W r) X
      ‖((cStar:ℂ)*star (dispersionModel S β u))*
        (mixedMassModel S β u V A-(cStar:ℂ)*dispersionModel S β u*squarefreeModelMass V A)‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  let hv : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hV hVpos hV'
  obtain ⟨K,hK,hbound⟩ := hv.mixedMassModel_error
  obtain ⟨E,a,hE,henergy⟩ := angular_logarithmic_dispersionAbsoluteModel_energy ℓ hW hR hlo hhi
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (negative_power_log_saving hc (a+k))
  have hcs := cStar_pos
  let C := cStar*K*(Fintype.card ι:ℝ)*E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,T₀,by positivity,?_⟩
  intro r X e u A hT₀ hL hX hprod hrough hA
  dsimp only
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  let M := dispersionAbsoluteModel S β
  have hM : 0 ≤ M := dispersionAbsoluteModel_nonneg S β
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hS : ∀ b ∈ S, primary b ∧ Squarefree b :=
    fun b hb => fullSquarefreePrimeSupport_primary R (W r) X e hb
  have hn : ∀ b ∈ S, (primaryPrimeFactors b).card ≤ Fintype.card ι := fun b hb =>
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R (W r) X) (Finset.mem_filter.mp hb).1
  have hp : ∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, (L r)^c ≤ norm p := by
    intro b hb p hpb
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R (W r) X
      (primaryPrimeFactor_spec (hS b hb).1 hpb).1
      (primaryPrimeFactor_spec (hS b hb).1 hpb).2 (Finset.mem_filter.mp hb).1
    have hw := ((fullPrimeSupport_mem_iff (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hhi r) i p).mp hi).2
    have hr : 1 ≤ norm p/X i := le_of_not_gt (fun hh => hw (hlo r i _ hh))
    exact (hrough i).le.trans (by simpa using
      (le_div_iff₀ (zero_lt_one.trans_le (hX i))).mp hr)
  have hb := hbound () S β u A ((L r)^c) (Fintype.card ι) hA
    (Real.rpow_pos_of_pos hLp _) hS hn hp
  have he := henergy r X e hL hX hprod
  have hlog : (1+Real.log (L r))^a*(L r)^(-c) ≤ 1/(1+Real.log (L r))^k := by
    apply (mul_le_mul_of_nonneg_left (hT (L r) hT₀) (pow_nonneg hz.le a)).trans_eq
    rw [pow_add]
    field_simp
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  calc
    _ ≤ (cStar*M)*(K*(Fintype.card ι:ℝ)*A^(2/3:ℝ)/(L r)^c*M) := by
      apply mul_le_mul _ hb (_root_.norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (norm_dispersionModel_le_absolute S β u) cStar_pos.le
    _ = (cStar*K*(Fintype.card ι:ℝ)*A^(2/3:ℝ)/(L r)^c)*M^2 := by ring
    _ ≤ (cStar*K*(Fintype.card ι:ℝ)*A^(2/3:ℝ)/(L r)^c)*
        (E*(L r)^(5/3:ℝ)*(1+Real.log (L r))^a) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*((1+Real.log (L r))^a*(L r)^(-c)) := by
      rw [Real.rpow_neg hLp.le]
      dsimp [C]
      ring
    _ ≤ C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ))*(1/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ (C+1)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
