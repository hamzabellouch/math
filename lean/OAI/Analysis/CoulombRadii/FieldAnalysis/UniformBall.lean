import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoulombBilinear

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def uniformBall (a M : ℝ) (x : Space) : ℝ :=
  (Metric.ball (0 : Space) a).indicator (fun _ => M / (4*Real.pi/3*a^3)) x

def ballCloud (y : Space) (a M : ℝ) (x : Space) : ℝ := uniformBall a M (x-y)

lemma uniformBall_nonneg {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (x : Space) :
    0 ≤ uniformBall a M x := by
  apply Set.indicator_nonneg
  intro x hx
  exact div_nonneg hM (by positivity)

lemma uniformBall_le {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (x : Space) :
    uniformBall a M x ≤ M/(4*Real.pi/3*a^3) := by
  exact Set.indicator_le_self' (fun _ _ => div_nonneg hM (by positivity)) _

lemma uniformBall_measurable (a M : ℝ) : Measurable (uniformBall a M) :=
  measurable_const.indicator measurableSet_ball

lemma uniformBall_integrable (a M : ℝ) : Integrable (uniformBall a M) := by
  exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const (C := M/(4*Real.pi/3*a^3)) measure_ball_lt_top.ne)

lemma uniformBall_mass {a : ℝ} (ha : 0 < a) (M : ℝ) :
    (∫ x, uniformBall a M x) = M := by
  unfold uniformBall
  rw [integral_indicator measurableSet_ball, integral_const]
  rw [measureReal_restrict_apply_univ, smul_eq_mul, volume_real_ball_three a ha.le]
  field_simp [ha.ne', Real.pi_ne_zero]

lemma uniformBall_power_integrable (a M : ℝ) :
    Integrable (fun x => uniformBall a M x^(5/3:ℝ)) := by
  have he : (fun x => uniformBall a M x^(5/3:ℝ)) =
      (Metric.ball (0:Space) a).indicator (fun _ => (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) := by
    funext x
    simp only [uniformBall,Set.indicator_apply]
    split <;> simp
  rw [he]
  exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const (C := (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) measure_ball_lt_top.ne)

lemma uniformBall_power {a : ℝ} (ha : 0 < a) (M : ℝ) :
    (∫ x, uniformBall a M x^(5/3:ℝ)) = (4*Real.pi/3*a^3)*(M/(4*Real.pi/3*a^3))^(5/3:ℝ) := by
  have he : (fun x => uniformBall a M x^(5/3:ℝ)) =
      (Metric.ball (0:Space) a).indicator (fun _ => (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) := by
    funext x
    simp only [uniformBall,Set.indicator_apply]
    split <;> simp
  rw [he, integral_indicator measurableSet_ball, integral_const]
  rw [measureReal_restrict_apply_univ, smul_eq_mul, volume_real_ball_three a ha.le]

lemma uniformBall_radial (a M : ℝ) (x : Space) :
    uniformBall a M x = uniformBall a M (EuclideanSpace.single 0 ‖x‖) := by
  simp only [uniformBall,Set.indicator_apply,Metric.mem_ball,dist_zero_right,
    PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x)]

lemma uniformBall_support (a M : ℝ) (x : Space) (hx : a < ‖x‖) :
    uniformBall a M x = 0 := by
  apply Set.indicator_of_notMem
  simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx.le

lemma ballCloud_mass {a : ℝ} (ha : 0 < a) (M : ℝ) (y : Space) :
    (∫ x, ballCloud y a M x) = M := by
  unfold ballCloud
  rw [integral_sub_right_eq_self, uniformBall_mass ha]

lemma ballCloud_integrable (a M : ℝ) (y : Space) : Integrable (ballCloud y a M) :=
  (uniformBall_integrable a M).comp_sub_right y

lemma ballCloud_measurable (a M : ℝ) (y : Space) : Measurable (ballCloud y a M) :=
  (uniformBall_measurable a M).comp (by fun_prop)

lemma ballCloud_coulomb {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y x : Space)
    (hxy : a ≤ ‖x-y‖) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) = M*coulombKernel (x-y) := by
  have he : (∫ z, coulombKernel (x-z)*ballCloud y a M z) =
      ∫ z, coulombKernel ((x-y)-z)*uniformBall a M z := by
    rw [← integral_sub_right_eq_self (fun z => coulombKernel ((x-y)-z)*uniformBall a M z) y]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change coulombKernel (x-z)*uniformBall a M (z-y) = _
      have hz : (x-y)-(z-y) = x-z := by abel
      dsimp only
      rw [hz])
  rw [he,radial_coulomb_integral_eq (uniformBall_integrable a M) (uniformBall_measurable a M)
    (uniformBall_nonneg ha hM) (uniformBall_le ha hM) (uniformBall_radial a M) ha.le
    (uniformBall_support a M) (by intro hh; simp [hh] at hxy; linarith) hxy,
    uniformBall_mass ha, mul_comm]

lemma ballCloud_coulomb_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y x : Space) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) ≤ (5/2:ℝ)*M/a := by
  have H := coulomb_convolution_bound (ballCloud_integrable a M y) (ballCloud_measurable a M y)
    (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha x
  rw [ballCloud_mass ha] at H
  convert H using 1
  field_simp [ha.ne', Real.pi_ne_zero]
  ring

lemma ballCloud_coulombBilinear_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space) :
    coulombBilinear (ballCloud y a M) (ballCloud y a M) ≤ (5/2:ℝ)*M^2/a := by
  have hi := ballCloud_integrable a M y
  have hm := ballCloud_measurable a M y
  have hb (z : Space) : ‖ballCloud y a M z‖ ≤ M/(4*Real.pi/3*a^3) := by
    change ‖uniformBall a M (z-y)‖ ≤ _
    rw [Real.norm_of_nonneg (uniformBall_nonneg ha hM (z-y))]
    exact uniformBall_le ha hM _
  rw [coulombBilinear_iterated hi hm hi hm hb]
  have hip : Integrable (fun z => ballCloud y a M z *
      (∫ w, coulombKernel (z-w)*ballCloud y a M w)) := by
    apply ((coulomb_pair_integrable hi hm hi hm hb).integral_prod_left).congr
    exact Eventually.of_forall (fun z => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun w => by ring))
  have H := integral_mono hip (hi.mul_const ((5/2:ℝ)*M/a)) (fun z =>
    mul_le_mul_of_nonneg_left (ballCloud_coulomb_bound ha hM y z) (uniformBall_nonneg ha hM (z-y)))
  rw [integral_mul_const,ballCloud_mass ha] at H
  calc
    _ ≤ M*((5/2:ℝ)*M/a) := H
    _ = (5/2:ℝ)*M^2/a := by ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma coreCoulombPotential_ballCloud {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ z ∈ A, a ≤ ‖z-y‖) :
    (∫ z, coreCoulombPotential u z*ballCloud y a M z) = M*coreCoulombPotential u y := by
  rw [coreCoulombPotential_fubini u _ (ballCloud_integrable a M y)]
  simp only [coreCoulombPotential,Finset.mul_sum,← integral_const_mul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have hz : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    rw [ballCloud_coulomb ha hM y (position x i) (hsep _ hz)]
    ring

lemma attraction_ballCloud {J : ℕ} (S : Nuclei J)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, attraction S z*ballCloud y a M z) = M*attraction S y := by
  have hi j : Integrable (fun z => S.charge j*(coulombKernel (S.position j-z)*ballCloud y a M z)) :=
    (coulomb_convolution_integrable (ballCloud_integrable a M y) (ballCloud_measurable a M y)
      (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha (S.position j)).const_mul _
  simp only [attraction,Finset.sum_mul,Finset.mul_sum]
  simp_rw [coulombKernel_sub_comm _ (S.position _), mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, ballCloud_coulomb ha hM y (S.position j) (hsep j)]
  ring

lemma coreScreenedField_ballCloud {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, coreScreenedField S u z*ballCloud y a M z) = M*coreScreenedField S u y := by
  have hi := ballCloud_integrable a M y
  have hn : Integrable (fun z => attraction S z*ballCloud y a M z) := by
    simp only [attraction,Finset.sum_mul]
    apply integrable_finsetSum
    intro j _
    have H := (coulomb_convolution_integrable hi (ballCloud_measurable a M y)
      (fun z => uniformBall_nonneg ha hM (z-y)) (fun z => uniformBall_le ha hM (z-y)) ha (S.position j)).const_mul (S.charge j)
    apply H.congr
    exact Eventually.of_forall (fun z => by dsimp only; rw [coulombKernel_sub_comm]; ring)
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub hn (coreCoulombPotential_mul_integrable u _ hi),attraction_ballCloud S ha hM y hnuc,
    coreCoulombPotential_ballCloud u hu ha hM y hcore]
  ring

end Coulomb

end

end OAI
