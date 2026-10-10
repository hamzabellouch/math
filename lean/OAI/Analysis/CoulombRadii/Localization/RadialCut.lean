import Mathlib
import OAI.Analysis.CoulombRadii.Localization.CutCombinatorics

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff
namespace Coulomb

def cutSeed (x : Space) : ℝ := Real.smoothTransition ((4-‖x‖^2)/3)
lemma cutSeed_smooth : ContDiff ℝ ∞ cutSeed := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 3)
lemma cutSeed_one (x : Space) (hx : ‖x‖ ≤ 1) : cutSeed x=1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [norm_nonneg x]
lemma cutSeed_zero (x : Space) (hx : 2 ≤ ‖x‖) : cutSeed x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]
lemma cutSeed_compact : HasCompactSupport cutSeed := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 2) (isCompact_closedBall 0 2)
  intro x hx
  exact cutSeed_zero x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using le_of_lt (show 2 < ‖x‖ by simpa using hx))

lemma cutSeed_derivative_bounded : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ cutSeed x‖ ≤ C := by
  obtain ⟨B,hB⟩ := (cutSeed_compact.fderiv ℝ).exists_bound_of_continuous
    (cutSeed_smooth.continuous_fderiv (by simp))
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x => (hB x).trans (le_max_left _ _)⟩
def cutSeedDerivativeBound : ℝ := Classical.choose cutSeed_derivative_bounded
lemma cutSeedDerivativeBound_pos : 0 < cutSeedDerivativeBound := (Classical.choose_spec cutSeed_derivative_bounded).1
lemma norm_cutSeed_derivative (x : Space) : ‖fderiv ℝ cutSeed x‖ ≤ cutSeedDerivativeBound :=
  (Classical.choose_spec cutSeed_derivative_bounded).2 x

def cutAngle (y : Space) (r : ℝ) (x : Space) : ℝ := (Real.pi/2)*cutSeed (r⁻¹ • (x-y))
lemma cutAngle_smooth (y : Space) (r : ℝ) : ContDiff ℝ ∞ (cutAngle y r) := by
  have ht : ContDiff ℝ ∞ (fun x : Space => r⁻¹ • (x-y)) := by fun_prop
  exact contDiff_const.mul (cutSeed_smooth.comp ht)
lemma cutAngle_fderiv (y : Space) (r : ℝ) (x v : Space) :
    fderiv ℝ (cutAngle y r) x v = (Real.pi/2)*r⁻¹*fderiv ℝ cutSeed (r⁻¹ • (x-y)) v := by
  have ht : HasFDerivAt (fun x : Space => r⁻¹ • (x-y))
      (r⁻¹ • (ContinuousLinearMap.id ℝ Space)) x := by
    convert ((hasFDerivAt_id x).sub_const y).const_smul r⁻¹ using 1
    rfl
  have h := (((cutSeed_smooth.differentiable (by simp) _).hasFDerivAt.comp x ht).const_mul (Real.pi/2)).fderiv
  have hh : fderiv ℝ (cutAngle y r) x =
      (Real.pi/2) • ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).comp (r⁻¹ • ContinuousLinearMap.id ℝ Space)) := by
    convert h using 1
    rfl
  rw [hh]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul]
  ring

def radialCut (y : Space) (r : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (cutAngle y r x) else Real.cos (cutAngle y r x)
lemma radialCut_smooth (y : Space) (r : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (radialCut y r l) := by
  unfold radialCut
  split_ifs
  · exact (cutAngle_smooth y r).sin
  · exact (cutAngle_smooth y r).cos
lemma radialCut_partition (y : Space) (r : ℝ) (x : Space) :
    ∑ l : Fin 2, radialCut y r l x ^ 2 = 1 := by
  simp [Fin.sum_univ_two,radialCut]
lemma radialCut_core_zero (y : Space) {r : ℝ} (hr : 0 < r) (x : Space) (hx : ‖x-y‖ ≤ r) :
    radialCut y r 1 x=0 := by
  have hs : ‖r⁻¹ • (x-y)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).2 hx
  simp [radialCut,cutAngle,cutSeed_one _ hs,Real.cos_pi_div_two]
lemma radialCut_out_zero (y : Space) {r : ℝ} (hr : 0 < r) (x : Space) (hx : 2*r ≤ ‖x-y‖) :
    radialCut y r 0 x=0 := by
  have hs : 2 ≤ ‖r⁻¹ • (x-y)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (le_inv_mul_iff₀ hr).2 (by simpa only [mul_comm] using hx)
  simp [radialCut,cutAngle,cutSeed_zero _ hs]

def radialCutCoefficient : ℝ := (Real.pi/2)*cutSeedDerivativeBound
lemma radialCutCoefficient_pos : 0 < radialCutCoefficient := by
  exact mul_pos (by positivity) cutSeedDerivativeBound_pos
lemma radialCut_derivative_bound (y : Space) {r : ℝ} (hr : 0 < r) (l : Fin 2)
    (b : Fin 3) (x : Space) :
    |fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r := by
  have hb : |fderiv ℝ (cutAngle y r) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r := by
    rw [cutAngle_fderiv,abs_mul,abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hr))]
    have H := ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).le_opNorm (EuclideanSpace.single b 1)).trans
      (mul_le_mul_of_nonneg_right (norm_cutSeed_derivative _) (norm_nonneg _))
    simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at H
    calc
      _ ≤ (Real.pi/2)*r⁻¹*cutSeedDerivativeBound := mul_le_mul_of_nonneg_left H (by positivity)
      _ = radialCutCoefficient/r := by unfold radialCutCoefficient; ring
  unfold radialCut
  split_ifs
  · rw [fderiv_sin ((cutAngle_smooth y r).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using hb)
  · rw [fderiv_cos ((cutAngle_smooth y r).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using hb)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
namespace Coulomb

lemma radialCut_fderiv_zero (y : Space) {r : ℝ} (hr : 0 < r) (l : Fin 2)
    (x : Space) (hx : 2*r < ‖x-y‖) : fderiv ℝ (radialCut y r l) x=0 := by
  have he : radialCut y r l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hh : ∀ᶠ z in 𝓝 x, 2*r < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    have hs : 2 ≤ ‖r⁻¹ • (z-y)‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (le_inv_mul_iff₀ hr).2 (by nlinarith)
    simp only [radialCut,cutAngle,cutSeed_zero _ hs,mul_zero,Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma radialCut_gradient_bound (y : Space) {r : ℝ} (hr : 0 < r) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(radialCutCoefficient/r)^2) * (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ Metric.closedBall y (2*r)
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (radialCutCoefficient/r)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg radialCutCoefficient_pos.le hr.le)).2
          (radialCut_derivative_bound y hr l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd := radialCut_fderiv_zero y hr
    have hh : 2*r < ‖x-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hx
    simp only [hd _ x hh,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

def expectedPopulation {n : ℕ} (ψ : H1Vector n) (A : Set Space) : ℝ :=
  ∑ s, ∑ i : Fin n, ∫ x, (A.indicator (fun _ => (1:ℝ)) (position x i))*‖ψ.value s x‖^2

lemma population_integrable {n : ℕ} (ψ : H1Vector n) (A : Set Space) (hA : MeasurableSet A)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => (A.indicator (fun _ => (1:ℝ)) (position x i))*‖ψ.value s x‖^2) := by
  have H := ((ψ.value_L2 s).integrable_norm_pow (by norm_num)).indicator (hA.preimage (positionCLM i).continuous.measurable)
  apply H.congr
  filter_upwards [] with x
  change (if position x i ∈ A then ‖ψ.value s x‖^2 else 0) = _
  by_cases hx : position x i ∈ A <;> simp [hx]

theorem form_radial_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {r : ℝ} (hr : 0 < r) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (radialCut y r) (radialCut_smooth y r)
      (radialCut_partition y r) (radialCutCoefficient/r) (div_nonneg radialCutCoefficient_pos.le hr.le)
      (radialCut_derivative_bound y hr) p)) ≤
      form S ψ+3*(radialCutCoefficient/r)^2*expectedPopulation ψ (Metric.closedBall y (2*r)) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(radialCutCoefficient/r)^2
  have hi s i := population_integrable ψ (Metric.closedBall y (2*r)) measurableSet_closedBall s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (radialCut y r l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right (radialCut_gradient_bound y hr a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (Metric.closedBall y (2*r)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb

end

end OAI
