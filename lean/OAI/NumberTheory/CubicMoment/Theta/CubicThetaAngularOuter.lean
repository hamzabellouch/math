import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUniformInverse
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAngularOuter

namespace OAI

/-! The fixed nonzero-angular Type-I height estimate for the original
Gauss sums. Finite level summation uses the actual coefficient L1 mass;
its logarithmic loss is absorbed only after the common exponent is chosen. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The source nonzero-angular high-height estimate, with the common
support threshold and the fixed far-left Gamma hypotheses explicit. -/
theorem angular_typeI_height_proved
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {W : Eisenstein → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {η : ℝ} (hη : 0 < η)
    (d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U → 1 ≤ T →
      T ≤ (R*U)^2 →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^d →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W r) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W r) U t‖))/T ≤
          K*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T := by
  have hh : 0 < η/2 := by positivity
  obtain ⟨C,hC,hmean⟩ :=
    hW.cubicTheta_inverted_angular_mean hMV hM ℓ hℓ hh (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound d hh
  refine ⟨C*A*L*2^(1/4:ℝ),by positivity,?_⟩
  intro S α R U T hR hU hsize hT hTX hS hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX2 : 2 ≤ R*U := (le_max_left _ _).trans hsize
  have hX : 1 ≤ R*U := by linarith
  have hXp : 0 < R*U := by positivity
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ R*U := le_mul_of_one_le_left hUp.le hR
  have hXsq : R*U ≤ (R*U)^2 := by nlinarith
  have hlow : (R*U)^(-(2:ℝ)) ≤ U := by
    calc
      _ ≤ (R*U)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = 1 := Real.rpow_zero _
      _ ≤ U := hU
  have hF : Real.exp hW.radius*U ≤ (R*U)^2 := by
    have hs := (le_max_right _ _).trans hsize
    nlinarith [mul_le_mul hs hUX hUp.le hXp.le]
  let B := C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ (W r) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ (W r) U t‖))/T ≤ B := by
    obtain ⟨hprim,_,hupper⟩ := hS r hr
    have hnr := norm_nonneg r
    by_cases hsf : Squarefree r
    · have hbound := hmean r r hprim hsf (R*U) U (Real.exp hW.radius*U) T
        hX hUp hT (by rw [Real.rpow_two]; nlinarith)
        (by simpa only [Real.rpow_two] using hTX) hlow
        (by simpa only [Real.rpow_two] using hUX.trans hXsq) le_rfl
        (by simpa only [Real.rpow_two] using hF)
      rw [add_comm] at hbound
      apply hbound.trans
      dsimp [B]
      gcongr
    · simp only [metaplecticAngularSmoothSum_zero_of_not_squarefree hprim hsf,
        norm_zero,intervalIntegral.integral_zero,add_zero,zero_div]
      exact hB
  rw [dyadic_finite_norm_sum S α (fun r => metaplecticAngularSmoothSum r ℓ (W r) U)
    (fun r _ => continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W r) hUp
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support r))]
  calc
    _ = ∑ r ∈ S, ‖α r‖*(((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ (W r) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ (W r) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ S, ‖α r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖α r‖) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ B*(A*R*(Real.log (R*U))^d) := mul_le_mul_of_nonneg_left hα hB
    _ = (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
        (R*U)^(η/2)*(Real.log (R*U))^d*Real.sqrt T := by dsimp [B]; ring
    _ ≤ (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
        (R*U)^(η/2)*(L*(R*U)^(η/2))*Real.sqrt T := by
      gcongr
      exact hlog _ hX
    _ = (C*A*L*2^(1/4:ℝ))*
        (Real.sqrt (R*U)*((R*U)^(η/2)*(R*U)^(η/2)))*R^(3/4:ℝ)*Real.sqrt T := by
      rw [angular_level_scaling hRp hUp]
      ring
    _ = _ := by
      rw [←Real.rpow_add hXp,show η/2+η/2=η by ring,
        Real.sqrt_eq_rpow,←Real.rpow_add hXp]

end CubicFirstMoment

end

end OAI
