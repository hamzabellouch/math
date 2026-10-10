import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.UniformBall

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma coreCoulombPotential_aestronglyMeasurable {k : ℕ} (u : H1Vector k) :
    AEStronglyMeasurable (coreCoulombPotential u) volume := by
  unfold coreCoulombPotential
  apply Finset.aestronglyMeasurable_fun_sum
  intro s hs
  apply Finset.aestronglyMeasurable_fun_sum
  intro i hi
  have hK : AEStronglyMeasurable (fun z : Configuration k × Space =>
      coulombKernel (position z.1 i-z.2)) (volume.prod volume) :=
    (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable
  exact (hK.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst).prod_swap.integral_prod_right'

lemma coreField_aestronglyMeasurable {J k : ℕ} (S : Nuclei J) (u : H1Vector k) :
    AEStronglyMeasurable (coreScreenedField S u) volume :=
  (attraction_measurable S).aestronglyMeasurable.sub (coreCoulombPotential_aestronglyMeasurable u)

lemma coreField_ballCloud_integrable {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => coreScreenedField S u z*ballCloud y a 1 z) := by
  have hn : Integrable (fun z => attraction S z*ballCloud y a 1 z) := by
    simp only [attraction,Finset.sum_mul]
    apply integrable_finsetSum
    intro j hj
    have H := (coulomb_convolution_integrable (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
      (fun z => uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => uniformBall_le ha zero_le_one (z-y)) ha (S.position j)).const_mul (S.charge j)
    apply H.congr
    exact Eventually.of_forall (fun z => by dsimp only; rw [coulombKernel_sub_comm]; ring)
  apply (hn.sub (coreCoulombPotential_mul_integrable u _ (ballCloud_integrable a 1 y))).congr
  filter_upwards [] with z
  change attraction S z*ballCloud y a 1 z-coreCoulombPotential u z*ballCloud y a 1 z = _
  unfold coreScreenedField
  ring

lemma coreField_positive_ballCloud_integrable {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => max (coreScreenedField S u z) 0*ballCloud y a 1 z) := by
  apply ((coreField_ballCloud_integrable S u ha y).sup (integrable_zero _ _ _)).congr
  filter_upwards [] with z
  change max (coreScreenedField S u z*ballCloud y a 1 z) 0 = _
  symm
  simpa only [zero_mul,ballCloud] using max_mul_of_nonneg (coreScreenedField S u z) 0 (uniformBall_nonneg ha zero_le_one (z-y))

lemma attraction_le_totalCharge_div {J : ℕ} (S : Nuclei J) {a : ℝ} (ha : 0 < a)
    (x : Space) (hsep : ∀ j, a ≤ ‖x-S.position j‖) : attraction S x ≤ totalCharge S/a := by
  unfold attraction totalCharge
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hK : coulombKernel (x-S.position j) ≤ 1/a := by
    simpa only [coulombKernel,one_div] using one_div_le_one_div_of_le ha (hsep j)
  exact (mul_le_mul_of_nonneg_left hK (le_trans zero_le_one (S.charge_ge_one j))).trans_eq (by ring)

lemma coreField_positive_square_ballCloud_integrable {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun z => (max (coreScreenedField S u z) 0)^2*ballCloud y a 1 z) := by
  have hm : AEStronglyMeasurable (fun z => (max (coreScreenedField S u z) 0)^2) volume :=
    ((coreField_aestronglyMeasurable S u).sup aestronglyMeasurable_const).pow 2
  apply ((ballCloud_integrable a 1 y).const_mul ((totalCharge S/a)^2)).mono'
    (hm.mul (ballCloud_measurable a 1 y).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(max (coreScreenedField S u z) 0)^2*ballCloud y a 1 z‖ ≤ _
  have hb : 0 ≤ ballCloud y a 1 z := uniformBall_nonneg ha zero_le_one (z-y)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hb)]
  by_cases hz : z-y ∈ Metric.ball (0:Space) a
  · have hdist : ‖z-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hsep (j : Fin J) : a ≤ ‖z-S.position j‖ := by
      have ht : ‖S.position j-y‖ ≤ ‖S.position j-z‖+‖z-y‖ := by simpa only [dist_eq_norm] using dist_triangle (S.position j) z y
      rw [norm_sub_rev (S.position j) z] at ht
      linarith [hnuc j]
    have hP : max (coreScreenedField S u z) 0 ≤ totalCharge S/a := by
      apply le_trans _ (attraction_le_totalCharge_div S ha z hsep)
      apply max_le _ (attraction_nonneg S z)
      unfold coreScreenedField
      linarith [coreCoulombPotential_nonneg u z]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hP 2)
      (uniformBall_nonneg ha zero_le_one (z-y))
  · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]

lemma ballCloud_nested_le {a : ℝ} (ha : 0 < a) (z w x : Space) (hw : ‖w-z‖ ≤ a) :
    ballCloud w a 1 x ≤ 8*ballCloud z (2*a) 1 x := by
  by_cases hx : x-w ∈ Metric.ball (0:Space) a
  · have hh : ‖x-w‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hxz : x-z ∈ Metric.ball (0:Space) (2*a) := by
      simp only [Metric.mem_ball,dist_zero_right]
      have ht : ‖x-z‖ ≤ ‖x-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle x w z
      linarith
    simp only [ballCloud,uniformBall,indicator_of_mem hx,indicator_of_mem hxz]
    have he : 1/(4*Real.pi/3*a^3) = 8*(1/(4*Real.pi/3*(2*a)^3)) := by ring
    exact he.le
  · simp only [ballCloud,uniformBall,indicator_of_notMem hx]
    exact mul_nonneg (by norm_num) (uniformBall_nonneg (by linarith) zero_le_one (x-z))

lemma square_weighted_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f ρ : X → ℝ) (hρ : Integrable ρ μ) (hp : ∀ x, 0 ≤ ρ x) (hm : (∫ x, ρ x ∂μ)=1)
    (h1 : Integrable (fun x => f x*ρ x) μ) (h2 : Integrable (fun x => f x^2*ρ x) μ) :
    (∫ x, f x*ρ x ∂μ)^2 ≤ ∫ x, f x^2*ρ x ∂μ := by
  let c : ℝ := ∫ x, f x*ρ x ∂μ
  have hsub : Integrable (fun x => f x^2*ρ x-(2*c)*(f x*ρ x)) μ := by
    exact h2.sub (h1.const_mul (2*c))
  have he : (∫ x, (f x-c)^2*ρ x ∂μ) = (∫ x, f x^2*ρ x ∂μ)-2*c^2+c^2 := by
    calc
      _ = ∫ x, (f x^2*ρ x-(2*c)*(f x*ρ x))+c^2*ρ x ∂μ :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by
        rw [integral_add hsub (hρ.const_mul (c^2)),
          integral_sub h2 (h1.const_mul _),integral_const_mul,integral_const_mul,hm]
        dsimp only [c]
        ring
  have h : 0 ≤ (∫ x, (f x-c)^2*ρ x ∂μ) := integral_nonneg (fun x => mul_nonneg (sq_nonneg (f x-c)) (hp x))
  rw [he] at h
  dsimp only [c] at h
  linarith

theorem coreField_positive_submean_square {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A) {a : ℝ} (ha : 0 < a) (z w : Space)
    (hw : ‖w-z‖ ≤ a) (hcore : ∀ x ∈ A, 4*a ≤ ‖x-z‖)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    (max (coreScreenedField S u w) 0)^2 ≤
      8*(∫ x, (max (coreScreenedField S u x) 0)^2*ballCloud z (2*a) 1 x) := by
  have hsep (x : Space) (hx : 4*a ≤ ‖x-z‖) : 2*a ≤ ‖x-w‖ := by
    have ht : ‖x-z‖ ≤ ‖x-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle x w z
    linarith
  have hci := coreField_ballCloud_integrable S u ha w
  have hpi := coreField_positive_ballCloud_integrable S u ha w
  have hsi := coreField_positive_square_ballCloud_integrable S u ha w (fun j => hsep _ (hnuc j))
  have hsz := coreField_positive_square_ballCloud_integrable S u (by linarith : 0 < 2*a) z
    (fun j => by linarith [hnuc j])
  have hmean : coreScreenedField S u w = ∫ x, coreScreenedField S u x*ballCloud w a 1 x := by
    simpa only [one_mul] using (coreScreenedField_ballCloud S u hu ha zero_le_one w
      (fun x hx => le_trans (by linarith) (hsep _ (hcore x hx)))
      (fun j => le_trans (by linarith) (hsep _ (hnuc j)))).symm
  have hpmean : max (coreScreenedField S u w) 0 ≤
      ∫ x, max (coreScreenedField S u x) 0*ballCloud w a 1 x := by
    apply max_le
    · rw [hmean]
      exact integral_mono hci hpi (fun x => mul_le_mul_of_nonneg_right (le_max_left _ _)
        (uniformBall_nonneg ha zero_le_one (x-w)))
    · exact integral_nonneg (fun x => mul_nonneg (le_max_right _ _) (uniformBall_nonneg ha zero_le_one (x-w)))
  calc
    _ ≤ (∫ x, max (coreScreenedField S u x) 0*ballCloud w a 1 x)^2 :=
      pow_le_pow_left₀ (le_max_right _ _) hpmean 2
    _ ≤ ∫ x, (max (coreScreenedField S u x) 0)^2*ballCloud w a 1 x :=
      square_weighted_mean_le volume _ _ (ballCloud_integrable a 1 w)
        (fun x => uniformBall_nonneg ha zero_le_one (x-w)) (ballCloud_mass ha 1 w) hpi hsi
    _ ≤ _ := by
      rw [← integral_const_mul]
      apply integral_mono hsi (hsz.const_mul 8)
      intro x
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (ballCloud_nested_le ha z w x hw)
        (sq_nonneg (max (coreScreenedField S u x) 0))

end Coulomb
end

end
end

end OAI
