import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianTailScale
import OAI.Probability.SKGap.Gaussian.GaussianTiltIdentity

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal

lemma scaled_weight_eq {n : ℕ} (r : ℝ) (x : Spin n) (g : Disorder n) :
    weight (fun e=>sqrt r*g e) 0 x=exp (∑ e,edgeCoefficient r x e*g e) := by
  unfold weight
  rw [edge_energy_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  unfold edgeCoefficient
  ring

lemma scaled_spin_weight_measurable {n : ℕ} (r : ℝ) (x : Spin n) :
    Measurable (fun g : Disorder n=>weight (fun e=>sqrt r*g e) 0 x) := by
  simp_rw [scaled_weight_eq]
  fun_prop

lemma scaled_spin_mass_measurable {n : ℕ} (r : ℝ) (x : Spin n) :
    Measurable (fun g : Disorder n=>mass (fun e=>sqrt r*g e) 0 x) :=
  (scaled_spin_weight_measurable r x).div ((partition_zero_measurable n).comp (by fun_prop))

lemma partition_mass_normalized {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (g : Disorder n) (x : Spin n) :
    gaussianSpinPartition n r g/(∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))*
      mass (fun e=>sqrt r*g e) 0 x =
      (1/(Fintype.card (Spin n):ℝ))*
      exp ((∑ e,edgeCoefficient r x e*g e)-(∑ e,edgeCoefficient r x e^2)/2) := by
  rw [gaussianSpinPartition_integral hr,edgeCoefficient_sq_sum hr]
  rw [mass,← gaussianSpinPartition_eq_partition,scaled_weight_eq,exp_sub]
  have hp := gaussianSpinPartition_pos n r g
  have hc : (Fintype.card (Spin n):ℝ) ≠ 0 := by positivity
  field_simp

theorem planted_joint_tilt {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (F : Spin n→Disorder n→ℝ≥0∞) (hF : ∀ x,Measurable (F x)) :
    (∫⁻ g, ENNReal.ofReal (gaussianSpinPartition n r g/
      (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n)))*
      ∑ x,ENNReal.ofReal (mass (fun e=>sqrt r*g e) 0 x)*F x (fun e=>sqrt r*g e)
      ∂gaussianCoordinates (Edge n)) =
    ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*∑ x : Spin n,
      ∫⁻ g,F x (fun e=>sqrt r*g e+r*spinValue (x e.1.1)*spinValue (x e.1.2))
        ∂gaussianCoordinates (Edge n) := by
  have hM : 0 < ∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n) :=
    gaussianSpinPartition_mean_pos hr
  simp_rw [Finset.mul_sum,← mul_assoc,← ENNReal.ofReal_mul (div_nonneg
    (gaussianSpinPartition_pos n r _).le hM.le),partition_mass_normalized hr,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(Fintype.card (Spin n):ℝ)),mul_assoc]
  rw [lintegral_finsetSum _ (fun x _=>by fun_prop)]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [gaussian_tilt_lintegral (edgeCoefficient r x) (fun g : Disorder n=>F x (fun e=>sqrt r*g e)) ((hF x).comp (by fun_prop))]
  apply lintegral_congr
  intro g
  congr 1
  ext e
  unfold edgeCoefficient
  calc
    _ = sqrt r*g e+(sqrt r)^2*(spinValue (x e.1.1)*spinValue (x e.1.2)) := by ring
    _ = _ := by rw [sq_sqrt hr]

theorem planted_disorder_joint_tilt {n : ℕ} (β : ℝ)
    (F : Spin n→Disorder n→ℝ≥0∞) (hF : ∀ x,Measurable (F x)) :
    (∫⁻ J,ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
      ∑ x,ENNReal.ofReal (mass J 0 x)*F x J ∂disorderLaw β n)=
    ENNReal.ofReal (1/(Fintype.card (Spin n):ℝ))*∑ x : Spin n,
      ∫⁻ g,F x (fun e=>sqrt (β^2/(n:ℝ))*g e+(β^2/(n:ℝ))*spinValue (x e.1.1)*spinValue (x e.1.2))
        ∂gaussianCoordinates (Edge n) := by
  have hmass (x : Spin n) : Measurable (fun J : Disorder n=>mass J 0 x) := by
    simpa only [sqrt_one,one_mul] using scaled_spin_mass_measurable 1 x
  have hi : Measurable (fun J : Disorder n=>
      ENNReal.ofReal (partition J 0/(∫ J,partition J 0 ∂disorderLaw β n))*
        ∑ x,ENNReal.ofReal (mass J 0 x)*F x J) :=
    ((partition_zero_measurable n).div_const _).ennreal_ofReal.mul
      (Finset.measurable_sum _ (fun x _=>(hmass x).ennreal_ofReal.mul (hF x)))
  rw [← (gaussian_disorder_hasLaw β n).lintegral_comp hi.aemeasurable]
  simpa only [disorder_partition_mean,← gaussianSpinPartition_eq_partition] using
    planted_joint_tilt (n:=n) (r:=β^2/(n:ℝ)) (by positivity) F hF
end SKGap
end
end

end OAI
