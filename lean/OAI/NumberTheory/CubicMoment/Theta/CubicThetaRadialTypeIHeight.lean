import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialDyadic
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAngularOuter

namespace OAI

/-! The required radial Type-I height mean, obtained directly from the
completed Voronoi formula and its finite inverse. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicTheta_radial_typeI_height
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {η : ℝ} (hη : 0 < η) (D d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → 1 ≤ T → T ≤ (R*U)^2 →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^d →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤
          K*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T+
            E*(R*U)^(5/6:ℝ)*(Real.log (R*U))^d/T^D := by
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨C,E,hC,hE,hmean⟩ := hW.cubicTheta_radial_dyadic_mean hMV hM hhalf D
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound d hhalf
  refine ⟨C*A*L*2^(1/4:ℝ),E*A,by positivity,by positivity,?_⟩
  intro w S α R U T hR hU hT hTX hS hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hXp : 0 < R*U := by positivity
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ R*U := le_mul_of_one_le_left hUp.le hR
  let B : ℝ := C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T+
    E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤ B := by
    obtain ⟨hprim,hlower,hupper⟩ := hS r hr
    have hnr := norm_nonneg r
    by_cases hsf : Squarefree r
    · have hbound := hmean (w r) r hprim hsf (R*U) U T hX hU hUX hT hTX
        (hupper.trans (by linarith))
      rw [add_comm] at hbound
      apply hbound.trans
      dsimp [B]
      apply add_le_add
      · gcongr
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRp hlower (by norm_num))
            (by positivity)) (pow_nonneg (zero_le_one.trans hT) _)
    · simp only [metaplecticAngularSmoothSum_zero_of_not_squarefree hprim hsf,
        norm_zero,intervalIntegral.integral_zero,add_zero,zero_div]
      exact hB
  rw [dyadic_finite_norm_sum S α (fun r => metaplecticAngularSmoothSum r 0 (W (w r)) U)
    (fun r _ => continuous_metaplecticAngularSmoothSum_of_cutoff r 0 (W (w r)) hUp
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r)))]
  have hmain : (C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T)*
      (A*R*(Real.log (R*U))^d) ≤
      (C*A*L*2^(1/4:ℝ))*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T := by
    calc
      _ = (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
          (R*U)^(η/2)*(Real.log (R*U))^d*Real.sqrt T := by ring
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
  have hpole : (E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*(A*R*(Real.log (R*U))^d) =
      (E*A)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^d/T^D := by
    calc
      _ = (E*A)*(U^(5/6:ℝ)*R^(-1/6:ℝ)*R)*(Real.log (R*U))^d/T^D := by ring
      _ = _ := by rw [typeI_residue_scaling hRp hUp]
  calc
    _ = ∑ r ∈ S, ‖α r‖*(((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ ∑ r ∈ S, ‖α r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖α r‖) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ B*(A*R*(Real.log (R*U))^d) := mul_le_mul_of_nonneg_left hα hB
    _ = (C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T)*(A*R*(Real.log (R*U))^d)+
        (E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*(A*R*(Real.log (R*U))^d) := by dsimp [B]; ring
    _ ≤ _ := by rw [hpole]; exact add_le_add hmain le_rfl

end CubicFirstMoment

end

end OAI
