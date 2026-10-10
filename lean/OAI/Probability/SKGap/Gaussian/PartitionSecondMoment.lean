import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianProductUpperTailLipschitz
import OAI.Probability.SKGap.Terminal.SpinGaussianBound
import OAI.Probability.SKGap.Gaussian.GaussianPartition

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

def quadraticGaussianBound (j : ℝ) : ℝ := ∫ g : ℝ, exp (j*g^2/2) ∂gaussianReal 0 1

lemma quadraticGaussianBound_ge_one {j : ℝ} (hj : 0 ≤ j) (hj1 : j < 1) :
    1 ≤ quadraticGaussianBound j := by
  have h := integral_mono (integrable_const (1:ℝ)) (gaussian_quadratic_integrable_sharp hj1)
    (fun g : ℝ=>one_le_exp (by positivity : 0 ≤ j*g^2/2))
  simpa [quadraticGaussianBound] using h

lemma gaussianSpinPartition_pos (n : ℕ) (r : ℝ) (g : Disorder n) :
    0 < gaussianSpinPartition n r g :=
  Finset.sum_pos (fun _ _=>exp_pos _) Finset.univ_nonempty

lemma gaussianSpinPartition_measurable (n : ℕ) (r : ℝ) : Measurable (gaussianSpinPartition n r) := by
  unfold gaussianSpinPartition
  exact Finset.measurable_sum _ (fun x _=>Real.measurable_exp.comp
    (Finset.measurable_sum _ (fun e _=>(measurable_pi_apply e).const_mul _)))

lemma gaussianSpinPartition_mean_pos {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    0 < ∫ g, gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n) := by
  rw [gaussianSpinPartition_integral hr]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) (exp_pos _)

lemma gaussianSpinPartition_second_moment {n : ℕ} {j r : ℝ} (hj : j < 1)
    (hr : 0 ≤ r) (hnr : (n:ℝ)*r ≤ j) :
    (∫ g,(gaussianSpinPartition n r g)^2 ∂gaussianCoordinates (Edge n)) ≤
      quadraticGaussianBound j*(∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))^2 := by
  rw [gaussianSpinPartition_square_integral hr,gaussianSpinPartition_integral hr]
  have hc : (Fintype.card (Spin n):ℝ)=(2:ℝ)^n := by simp [Spin]
  have he : exp (r*(Fintype.card (Edge n):ℝ)-r*(n:ℝ)/2) ≤ exp (r*(Fintype.card (Edge n):ℝ)) :=
    exp_le_exp.mpr (by nlinarith [mul_nonneg hr (show (0:ℝ) ≤ n by positivity)])
  have hb := spin_quadratic_sum_bound hj hr hnr
  rw [← hc] at hb
  have hB : 0 ≤ quadraticGaussianBound j := integral_nonneg (fun _=>(exp_pos _).le)
  have hc0 : (0:ℝ) ≤ Fintype.card (Spin n) := by positivity
  calc
    _ ≤ (Fintype.card (Spin n):ℝ)*exp (r*(Fintype.card (Edge n):ℝ)-r*(n:ℝ)/2)*
        ((Fintype.card (Spin n):ℝ)*quadraticGaussianBound j) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (Fintype.card (Spin n):ℝ)*exp (r*(Fintype.card (Edge n):ℝ))*
        ((Fintype.card (Spin n):ℝ)*quadraticGaussianBound j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hc0) (mul_nonneg hc0 hB)
    _ = _ := by
      have h : exp (r*(Fintype.card (Edge n):ℝ))=exp (r*(Fintype.card (Edge n):ℝ)/2)^2 := by
        rw [← exp_nat_mul];congr 1;ring
      rw [h];ring

lemma gaussianSpinPartition_positive_probability {n : ℕ} {j r : ℝ} (hj0 : 0 ≤ j)
    (hj : j < 1) (hr : 0 ≤ r) (hnr : (n:ℝ)*r ≤ j) :
    1/(4*quadraticGaussianBound j) ≤ (gaussianCoordinates (Edge n)).real
      {g | (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))/2 ≤ gaussianSpinPartition n r g} := by
  exact second_moment_positive_probability _ _ (gaussianSpinPartition_measurable n r)
    (gaussianSpinPartition_integrable n r) (gaussianSpinPartition_square_integrable n r)
    (gaussianSpinPartition_mean_pos hr) (lt_of_lt_of_le zero_lt_one (quadraticGaussianBound_ge_one hj0 hj))
    rfl (gaussianSpinPartition_second_moment hj hr hnr)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal

lemma log_sum_exp_order {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι→ℝ) (d : ℝ) (h : ∀ i,f i ≤ g i+d) :
    log (∑ i,exp (f i)) ≤ log (∑ i,exp (g i))+d := by
  have hp : 0 < ∑ i,exp (f i) := Finset.sum_pos (fun i _=>exp_pos _) Finset.univ_nonempty
  have hq : 0 < ∑ i,exp (g i) := Finset.sum_pos (fun i _=>exp_pos _) Finset.univ_nonempty
  have hh : (∑ i,exp (f i)) ≤ (∑ i,exp (g i))*exp d := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _=> (exp_le_exp.mpr (h i)).trans_eq (exp_add _ _))
  have he := log_le_log hp hh
  rw [log_mul hq.ne' (exp_pos _).ne',log_exp] at he
  exact he

lemma log_sum_exp_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    {E : Type*} [PseudoMetricSpace E] (f : ι→E→ℝ) {L : ℝ≥0}
    (hf : ∀ i,LipschitzWith L (f i)) :
    LipschitzWith L (fun x=>log (∑ i,exp (f i x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_le]
  constructor
  · have hh := log_sum_exp_order (fun i=>f i y) (fun i=>f i x) ((L:ℝ)*dist x y)
      (fun i=>by have hh := (hf i).dist_le_mul y x;rw [Real.dist_eq,dist_comm y x] at hh
                 linarith only [le_abs_self (f i y-f i x),hh])
    linarith only [hh]
  · have hh := log_sum_exp_order (fun i=>f i x) (fun i=>f i y) ((L:ℝ)*dist x y)
      (fun i=>by have hh := (hf i).dist_le_mul x y;rw [Real.dist_eq] at hh
                 linarith only [le_abs_self (f i x-f i y),hh])
    linarith only [hh]

lemma gaussianProduct_lower_tail_lipschitz {κ : Type*} [Fintype κ]
    {f : (κ→ℝ)→ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1)).real
      {x | f x-∫ y,f y ∂Measure.pi (fun _ : κ=>gaussianReal 0 1) ≤ -u} ≤
      exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  have hn : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>-f x.ofLp) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,neg_sub_neg,abs_sub_comm] using hf.dist_le_mul x y
  have h := gaussianProduct_upper_tail_lipschitz (f:=fun x=>-f x) hn hL hu
  simp only [integral_neg] at h
  convert h using 2
  ext x;simp only [mem_ofPred_eq];constructor <;> intro hx <;> linarith only [hx]

lemma gaussian_log_anchor {κ : Type*} [Fintype κ]
    {f : (κ→ℝ)→ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>f x.ofLp))
    (hL : 0 < L) {p b c : ℝ} (hc : 0 < c)
    (hpc : exp (-2*c^2/π^2) < p)
    (hp : p ≤ (Measure.pi (fun _ : κ=>gaussianReal 0 1)).real {x | b ≤ f x}) :
    b-c*(L:ℝ) ≤ ∫ y,f y ∂Measure.pi (fun _ : κ=>gaussianReal 0 1) := by
  by_contra hh
  have hs : {x | b ≤ f x} ⊆ {x | c*(L:ℝ) ≤ f x-∫ y,f y ∂Measure.pi (fun _ : κ=>gaussianReal 0 1)} := by
    intro x hx;dsimp only [mem_ofPred_eq] at *;linarith only [not_le.mp hh,hx]
  have ht := gaussianProduct_upper_tail_lipschitz hf hL (mul_nonneg hc.le (NNReal.coe_nonneg L))
  have he : -2*(c*(L:ℝ))^2/(π^2*(L:ℝ)^2)= -2*c^2/π^2 := by
    have hLr : (L:ℝ) ≠ 0 := ne_of_gt hL
    field_simp
  rw [he] at ht
  have hm := measureReal_mono hs (measure_ne_top (Measure.pi (fun _ : κ=>gaussianReal 0 1)) _)
  linarith only [hp,ht,hm,hpc]
end SKGap
end
end

end OAI
