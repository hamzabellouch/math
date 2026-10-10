import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedModelNorm
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.MixedModelCoprime
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! Coprimality removal in the literal stopped mixed model. Roughness is
required only at nonzero coefficients; the original support is retained. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_mixed_model_log_saving (ℓ : ℤ) {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hκ : 0 < κ) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦpos : tsupport Φ ⊆ Set.Ioi 0) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b A u : ℝ), 0 < δ → δ ≤ 1 → X^κ ≤ b → b ≤ X → 0 < A →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (e : Eisenstein) (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖((cStar:ℂ)*star (dispersionModel S β u))*(mixedMassModel S β u Φ A-
        (cStar:ℂ)*dispersionModel S β u*squarefreeModelMass Φ A)‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hv : UniformLogWeights (fun _ : Unit => Φ) := uniformLogWeights_constant Φ hΦ hΦpos hΦ'
  obtain ⟨K,hK,herror⟩ := hv.active_mixedMassModel_error
  obtain ⟨M,hM,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  have hcs : 0 < cStar := cStar_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := 18*(2:ℝ)^(1/6:ℝ)*M
  let E := cStar*K*D^2/Real.log 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E+1,by positivity,?_⟩
  filter_upwards [hcoeff,(tendsto_rpow_atTop hκ).eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1)] with X hcoeff hlarge hX
  intro δ b A u hδ hδone hbX hbXhi hA W hW e j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let R := min (X^ξ) (geometricBinLower (1+δ) X h)
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hbp : 0 < b := zero_lt_one.trans_le (hlarge.trans hbX)
  have hRp : 0 < R := (pow_pos hLp (k+1)).trans_le hR
  have hS (a : Eisenstein) (ha : a ∈ S) := stoppedIntervalSupport_spec X (b/2) b e ha
  have hc : ∀ a ∈ S, ‖β a‖ ≤ M := (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hAbs : 0 ≤ dispersionAbsoluteModel S β := dispersionAbsoluteModel_nonneg S β
  have hm : dispersionAbsoluteModel S β ≤ D*b^(5/6:ℝ) :=
    bounded_annular_absolute_model S β hbp hM.le (fun a ha =>
      ⟨(hS a ha).1,(Finset.mem_filter.mp ha).2.2.2.1.le,(hS a ha).2.2⟩) hc
  have hcard (a : Eisenstein) (ha : a ∈ S) (_hz : β a ≠ 0) :
      ((primaryPrimeFactors a).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log (hS a ha).1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log
        (norm_pos_of_ne_zero (primary_ne_zero (hS a ha).1))
        ((hS a ha).2.2.trans hbXhi)) (Real.log_pos (by norm_num)).le)
  have hr (a : Eisenstein) (_ha : a ∈ S) (hz : β a ≠ 0)
      (p : Eisenstein) (hp : p ∈ primaryPrimeFactors a) : R ≤ norm p :=
    angularStoppedRowCoefficient_early_roughness ℓ X (X^ξ) (X^(2/5:ℝ)) 0 (1+δ) Z Q W
      (Real.rpow_pos_of_pos hXp _) (Real.rpow_le_rpow_of_exponent_le hX1 hξz)
      (by linarith) (by linarith) j₀ k₀ h early hj hz
      (primaryPrimeFactor_spec (hS a _ha).1 hp).1 (primaryPrimeFactor_spec (hS a _ha).1 hp).2
  have he := herror () S β u A R (Real.log X/Real.log 2) hA hRp (by positivity)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hcard hr
  have hlog : Real.log X/R ≤ 1/(Real.log X)^k := by
    apply (div_le_div_of_nonneg_left hLp.le (pow_pos hLp _) hR).trans_eq
    rw [pow_succ]
    field_simp
  change ‖((cStar:ℂ)*star (dispersionModel S β u))*_‖ ≤ _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  calc
    _ ≤ (cStar*dispersionAbsoluteModel S β)*(K*(Real.log X/Real.log 2)*A^(2/3:ℝ)/R*
        dispersionAbsoluteModel S β) := mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_dispersionModel_le_absolute S β u) cStar_pos.le)
      he (_root_.norm_nonneg _) (by positivity)
    _ = (cStar*K/Real.log 2)*A^(2/3:ℝ)*(dispersionAbsoluteModel S β)^2*(Real.log X/R) := by ring
    _ ≤ (cStar*K/Real.log 2)*A^(2/3:ℝ)*(D*b^(5/6:ℝ))^2*(1/(Real.log X)^k) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (dispersionAbsoluteModel_nonneg S β) hm 2) (by positivity)
      · exact hlog
      · positivity
      · positivity
    _ = E*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
      rw [mul_pow,←Real.rpow_mul_natCast hbp.le]
      norm_num
      dsimp [E]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : E ≤ E+1)
          (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hLp.le _)

end CubicFirstMoment

end

end OAI
