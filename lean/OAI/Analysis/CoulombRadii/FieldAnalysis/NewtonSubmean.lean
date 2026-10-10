import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel
import OAI.Analysis.CoulombRadii.FieldAnalysis.FarSubmean

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma ballCloud_coulomb_le {a M : ℝ} (ha : 0<a) (hM : 0≤M) (y x : Space) (hxy : x≠y) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) ≤ M*coulombKernel (x-y) := by
  have he : (∫ z, coulombKernel (x-z)*ballCloud y a M z) =
      ∫ z, coulombKernel ((x-y)-z)*uniformBall a M z := by
    rw [← integral_sub_right_eq_self (fun z => coulombKernel ((x-y)-z)*uniformBall a M z) y]
    apply integral_congr_ae
    filter_upwards [] with z
    change coulombKernel (x-z)*uniformBall a M (z-y) = _
    rw [show (x-y)-(z-y)=x-z by abel]
  rw [he]
  have H := radial_coulomb_integral_le (uniformBall_integrable a M) (uniformBall_measurable a M)
    (uniformBall_nonneg ha hM) (uniformBall_le ha hM) (uniformBall_radial a M) (sub_ne_zero.mpr hxy)
  simpa only [uniformBall_mass ha,mul_comm M] using H

lemma potentialOf_ballCloud_integrable {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun z => NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))).integral_prod_right
  apply H.congr
  filter_upwards [] with z
  simp only [NeutralAtom.potentialOf,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  change ρ x*ballCloud y a 1 z*coulombKernel (x-z) = coulombKernel (z-x)*ρ x*ballCloud y a 1 z
  rw [coulombKernel_sub_comm x z]
  ring

lemma potentialOf_ballCloud_le {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) ≤ NeutralAtom.potentialOf ρ y := by
  have H := coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))
  have he : (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) =
      ∫ x, ∫ z, ρ x*ballCloud y a 1 z*coulombKernel (x-z) := by
    rw [integral_integral_swap H]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [NeutralAtom.potentialOf,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    change coulombKernel (z-x)*ρ x*ballCloud y a 1 z = ρ x*ballCloud y a 1 z*coulombKernel (x-z)
    rw [coulombKernel_sub_comm z x]
    ring
  rw [he]
  apply integral_mono_ae H.integral_prod_left hK
  filter_upwards [volume.ae_ne y] with x hxy
  have hh := mul_le_mul_of_nonneg_left (ballCloud_coulomb_le ha zero_le_one y x hxy) (hp x)
  simpa only [←integral_const_mul,one_mul,coulombKernel_sub_comm y x,mul_left_comm,mul_comm,mul_assoc] using hh

lemma screenedPotential_ballCloud_submean {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ) (hp : ∀ x, 0≤ρ x)
    {a : ℝ} (ha : 0<a) (y : Space)
    (hcore : ∀ z ∈ A, a≤‖z-y‖) (hnuc : ∀ j, a≤‖S.position j-y‖)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    coreScreenedField S u y-NeutralAtom.potentialOf ρ y ≤
      ∫ z, (coreScreenedField S u z-NeutralAtom.potentialOf ρ z)*ballCloud y a 1 z := by
  have hc : Integrable (fun z => coreScreenedField S u z*ballCloud y a 1 z) := by
    apply ((attraction_ballCloud_integrable S ha y).sub
      (coreCoulombPotential_mul_integrable u _ (ballCloud_integrable a 1 y))).congr
    filter_upwards [] with z
    change attraction S z*ballCloud y a 1 z-coreCoulombPotential u z*ballCloud y a 1 z = _
    rw [coreScreenedField,sub_mul]
  simp_rw [sub_mul]
  rw [integral_sub hc (potentialOf_ballCloud_integrable hi hm ha y),
    coreScreenedField_ballCloud S u hu ha zero_le_one y hcore hnuc,one_mul]
  linarith [potentialOf_ballCloud_le hi hm hp ha y hK]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma closedBall_ae_ball (y : Space) (a : ℝ) :
    Metric.closedBall y a =ᵐ[volume] Metric.ball y a := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume y a)] with x hx
  apply propext
  simp only [Metric.mem_closedBall,Metric.mem_ball,Metric.mem_sphere] at *
  exact ⟨fun h => lt_of_le_of_ne h hx,le_of_lt⟩

lemma integral_ballCloud (F : Space → ℝ) (y : Space) (a : ℝ) :
    (∫ x, F x*ballCloud y a 1 x) =
      (4*Real.pi/3*a^3)⁻¹*(∫ x in Metric.closedBall y a, F x) := by
  have he : (fun x => F x*ballCloud y a 1 x) =
      (Metric.ball y a).indicator (fun x => F x*(4*Real.pi/3*a^3)⁻¹) := by
    funext x
    have hd : x-y∈Metric.ball (0:Space) a ↔ x∈Metric.ball y a := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero]
    by_cases hx : x∈Metric.ball y a
    · simp only [ballCloud,uniformBall,indicator_of_mem hx,indicator_of_mem (hd.mpr hx),one_div]
    · simp only [ballCloud,uniformBall,indicator_of_notMem hx,indicator_of_notMem (not_congr hd |>.mpr hx),mul_zero]
  rw [he,integral_indicator measurableSet_ball,integral_mul_const,
    ←setIntegral_congr_set (closedBall_ae_ball y a),mul_comm]

lemma integral_closedBall_affine (F : Space → ℝ) (y : Space) {a : ℝ} (ha : 0<a) (r : ℝ) :
    (∫ z in Metric.closedBall (0:Space) r, F (y+a • z)) =
      (a^3)⁻¹*(∫ x in Metric.closedBall y (a*r), F x) := by
  let g := (Metric.closedBall y (a*r)).indicator F
  have he (z : Space) : g (y+a • z) =
      (Metric.closedBall (0:Space) r).indicator (fun x => F (y+a • x)) z := by
    have hz : y+a • z∈Metric.closedBall y (a*r) ↔ z∈Metric.closedBall (0:Space) r := by
      simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos ha,sub_zero]
      exact mul_le_mul_iff_right₀ ha
    by_cases h : z∈Metric.closedBall (0:Space) r
    · simp only [g,indicator_of_mem h,indicator_of_mem (hz.mpr h)]
    · simp only [g,indicator_of_notMem h,indicator_of_notMem (not_congr hz |>.mpr h)]
  have hh := Measure.integral_comp_smul_of_nonneg volume (fun x => g (y+x)) a (hR:=ha.le)
  simp only [Space,finrank_euclideanSpace_fin,smul_eq_mul] at hh
  simp_rw [he] at hh
  rw [integral_indicator measurableSet_closedBall,integral_add_left_eq_self] at hh
  simpa only [g,integral_indicator measurableSet_closedBall] using hh

lemma volume_closedBall_three (y : Space) {r : ℝ} (hr : 0≤r) :
    volume.real (Metric.closedBall y r) = 4*Real.pi/3*r^3 := by
  rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_ball_center,volume_real_ball_three r hr]

lemma submean_affine {F : Space → ℝ} (y : Space) {a : ℝ} (ha : 0<a)
    (hm : F y ≤ ∫ x, F x*ballCloud y (2*a) 1 x) :
    volume.real (Metric.closedBall (0:Space) 2)*(a^4*F y) ≤
      ∫ z in Metric.closedBall (0:Space) 2, a^4*F (y+a • z) := by
  rw [integral_ballCloud] at hm
  rw [integral_const_mul,integral_closedBall_affine F y ha,volume_closedBall_three _ (by norm_num)]
  have hV : 0<4*Real.pi/3*(2*a)^3 := by positivity
  have hi : (4*Real.pi/3*(2*a)^3)*F y ≤ (∫ x in Metric.closedBall y (2*a), F x) := by
    have hh := mul_le_mul_of_nonneg_left hm hV.le
    simpa only [←mul_assoc,mul_inv_cancel₀ hV.ne',one_mul] using hh
  have hh := mul_le_mul_of_nonneg_left hi (show 0≤a^4*(a^3)⁻¹ by positivity)
  rw [show a*2=2*a by ring]
  convert hh using 1 <;> first | rfl | field_simp [ha.ne']

end Coulomb

end

end OAI
