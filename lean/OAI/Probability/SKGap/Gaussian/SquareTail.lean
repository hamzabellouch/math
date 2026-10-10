import Mathlib
import OAI.Probability.SKGap.Gaussian.StandardGaussianProduct
import OAI.Probability.SKGap.Localization.EmpiricalLaw
import OAI.Probability.SKGap.Matrix.NormalLogConst

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma gaussian_exp_quadratic_integrable {d α : ℝ} {s : ℝ≥0} (hs : 0 < s)
    (hα : α < 1/(4*(s:ℝ))) :
    Integrable (fun y => exp (α*y^2)) (gaussianReal d s) := by
  rw [gaussianReal_of_var_ne_zero d (ne_of_gt hs), integrable_withDensity_iff
    (measurable_gaussianPDF d s) (ae_of_all _ (fun y => by simp [gaussianPDF]))]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  let c : ℝ := 1/(4*(s:ℝ))-α
  have hsp : 0 < (s:ℝ) := hs
  have hc : 0 < c := sub_pos.mpr hα
  have hi := (integrable_exp_neg_mul_sq hc).const_mul
    ((1/sqrt (2*Real.pi*(s:ℝ)))*exp (d^2/(2*(s:ℝ))))
  apply hi.mono' (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (gaussianPDFReal_nonneg _ _ _))]
  unfold gaussianPDFReal
  have hbound : α*y^2 + -(y-d)^2/(2*(s:ℝ)) ≤ d^2/(2*(s:ℝ))-c*y^2 := by
    dsimp [c]
    field_simp
    nlinarith [sq_nonneg (y-2*d)]
  calc
    _ = (1/sqrt (2*Real.pi*(s:ℝ)))*exp (α*y^2 + -(y-d)^2/(2*(s:ℝ))) := by rw [exp_add]; ring
    _ ≤ (1/sqrt (2*Real.pi*(s:ℝ)))*exp (d^2/(2*(s:ℝ))-c*y^2) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hbound) (by positivity)
    _ = _ := by simp only [sub_eq_add_neg,exp_add,neg_mul,mul_assoc]

def squareTail (R y : ℝ) : ℝ := if R < |y| then y^2 else 0

lemma measurable_squareTail (R : ℝ) : Measurable (squareTail R) := by
  unfold squareTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
    (measurable_id.pow_const 2) measurable_const

lemma squareTail_nonneg (R y : ℝ) : 0 ≤ squareTail R y := by
  unfold squareTail
  split_ifs <;> positivity

lemma squareTail_le (R y : ℝ) : squareTail R y ≤ y^2 := by
  unfold squareTail
  split_ifs <;> nlinarith [sq_nonneg y]

lemma tendsto_squareTail (y : ℝ) : Tendsto (fun R => squareTail R y) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop |y|] with R hR
  exact (ite_eq_right (not_lt.mpr hR)).symm

lemma tendsto_gaussian_tail_tilt (f : ℝ →ᵇ ℝ) {d α : ℝ} {s : ℝ≥0}
    (hs : 0 < s) (hα0 : 0 ≤ α) (hα : α < 1/(4*(s:ℝ))) :
    Tendsto (fun R => ∫ y, exp (f y+α*squareTail R y) ∂gaussianReal d s)
      atTop (𝓝 (∫ y, exp (f y) ∂gaussianReal d s)) := by
  let bound : ℝ → ℝ := fun y => exp ‖f‖*exp (α*y^2)
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall (fun R =>
      ((f.continuous.measurable.add ((measurable_squareTail R).const_mul α)).exp).aestronglyMeasurable)
  · exact Eventually.of_forall (fun R => ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      dsimp [bound]
      rw [← exp_add]
      apply exp_le_exp.mpr
      exact add_le_add ((le_abs_self _).trans (f.norm_coe_le_norm y))
        (mul_le_mul_of_nonneg_left (squareTail_le R y) hα0)))
  · exact (gaussian_exp_quadratic_integrable hs hα).const_mul _
  · exact ae_of_all _ (fun y => by
      have h := (tendsto_const_nhds (x := f y)).add ((tendsto_squareTail y).const_mul α)
      simpa only [mul_zero, add_zero,Function.comp_def] using (continuous_exp.tendsto _).comp h)

end SKGap

namespace SKGap
lemma integrable_gaussian_tail_test (f : ℝ →ᵇ ℝ) {d α : ℝ} {s : ℝ≥0}
    (hs : 0 < s) (hα0 : 0 ≤ α) (hα : α < 1/(4*(s:ℝ))) (R : ℝ) :
    Integrable (fun y => exp (f y+α*squareTail R y)) (gaussianReal d s) := by
  apply ((gaussian_exp_quadratic_integrable hs hα).const_mul (exp ‖f‖)).mono'
    (((f.continuous.measurable.add ((measurable_squareTail R).const_mul α)).exp).aestronglyMeasurable)
  exact ae_of_all _ (fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),← exp_add]
    apply exp_le_exp.mpr
    exact add_le_add ((le_abs_self _).trans (f.norm_coe_le_norm y))
      (mul_le_mul_of_nonneg_left (squareTail_le R y) hα0))

lemma product_general_test_integrable {ι : Type*} [Fintype ι] {g : ℝ → ℝ} {d s : ℝ}
    (hs : 0 < s) (hg : Integrable (fun y => exp (g y)) (gaussianReal d s.toNNReal)) :
    Integrable (fun y : ι → ℝ => exp (∑ i, g (y i))*productNormal d s y) := by
  have h := Integrable.fintype_prod (fun _ : ι =>
    (integrable_gaussian_iff (ne_of_gt (Real.toNNReal_pos.mpr hs))).mp hg)
  simpa only [exp_sum,productNormal,Finset.prod_mul_distrib,volume_pi,mul_comm] using h

lemma product_general_test_integral {ι : Type*} [Fintype ι] {g : ℝ → ℝ} {d s : ℝ}
    (hs : 0 < s) (hg : Integrable (fun y => exp (g y)) (gaussianReal d s.toNNReal)) :
    (∫ y : ι → ℝ, exp (∑ i, g (y i))*productNormal d s y) =
      exp ((Fintype.card ι:ℝ)*log (∫ x, exp (g x) ∂gaussianReal d s.toNNReal)) := by
  have hz : 0 < ∫ x, exp (g x) ∂gaussianReal d s.toNNReal :=
    (integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le) hg).mpr
      (by simp [Function.support,(exp_pos _).ne'])
  have he (y : ι → ℝ) : exp (∑ i, g (y i))*productNormal d s y =
      ∏ i, exp (g (y i))*gaussianPDFReal d s.toNNReal (y i) := by
    rw [exp_sum,productNormal,Finset.prod_mul_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (g x)*gaussianPDFReal d s.toNNReal x)]
  have hnorm : (∫ x, exp (g x)*gaussianPDFReal d s.toNNReal x) =
      ∫ x, exp (g x) ∂gaussianReal d s.toNNReal := by
    rw [integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr hs))]
    simp only [smul_eq_mul,mul_comm]
  rw [hnorm,exp_nat_mul,exp_log hz]

theorem gaussian_covered_tail_laplace {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : Type*} (C : Finset X) (f : X → ℝ →ᵇ ℝ) (d₀ s₀ : X → ℝ)
    (hs₀ : ∀ x ∈ C, 0 < s₀ x) (d s ψ : (ι → ℝ) → ℝ)
    (R r ε α ν R₁ : ℝ) (hα : 0 ≤ α) {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hpos : ∀ y ∈ E, 0 < s y)
    (hmom : ∀ y ∈ E, ∑ i, (y i)^2 ≤ (Fintype.card ι:ℝ)*R)
    (htail : ∀ y ∈ E, (Fintype.card ι:ℝ)*ν ≤ ∑ i, squareTail R₁ (y i))
    (hi : ∀ x ∈ C, Integrable (fun y => exp (f x y+α*squareTail R₁ y))
      (gaussianReal (d₀ x) (s₀ x).toNNReal))
    (hinc : ∀ x ∈ C, log (∫ y, exp (f x y+α*squareTail R₁ y)
      ∂gaussianReal (d₀ x) (s₀ x).toNNReal) ≤
      log (∫ y, exp (f x y) ∂gaussianReal (d₀ x) (s₀ x).toNNReal)+ε)
    (hcover : ∀ y ∈ E, ∃ x ∈ C,
      ψ y-(∫ u, f x u ∂empiricalLaw y)+normalDensityError R (d y) (s y) (d₀ x) (s₀ x)+
        log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal) < r) :
    (∫⁻ y in E, ENNReal.ofReal (exp ((Fintype.card ι:ℝ)*ψ y)*productNormal (d y) (s y) y)) ≤
      ENNReal.ofReal ((C.card:ℝ)*exp ((Fintype.card ι:ℝ)*(r+ε-α*ν))) := by
  classical
  let F (x : X) (y : ι → ℝ) : ℝ :=
    exp ((Fintype.card ι:ℝ)*(r-α*ν)-(Fintype.card ι:ℝ)*
      log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal)) *
      (exp (∑ i, (f x (y i)+α*squareTail R₁ (y i)))*productNormal (d₀ x) (s₀ x) y)
  have hFi (x : X) (hx : x ∈ C) : Integrable (F x) :=
    (product_general_test_integrable (hs₀ x hx) (hi x hx)).const_mul _
  have hFnn (x : X) (y : ι → ℝ) : 0 ≤ F x y :=
    mul_nonneg (exp_pos _).le (mul_nonneg (exp_pos _).le (productNormal_nonneg _ _ _))
  have hnorm (x : X) (hx : x ∈ C) :
      ∫ y, F x y ≤ exp ((Fintype.card ι:ℝ)*(r+ε-α*ν)) := by
    dsimp [F]
    rw [integral_const_mul,product_general_test_integral (hs₀ x hx) (hi x hx),← exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hinc x hx) (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ _)
    nlinarith
  have hdom (y : ι → ℝ) (hy : y ∈ E) :
      exp ((Fintype.card ι:ℝ)*ψ y)*productNormal (d y) (s y) y ≤ ∑ x ∈ C, F x y := by
    obtain ⟨x,hx,hc⟩ := hcover y hy
    have hdens := normalLogDensity_sum_sub_le (hmom y hy) (d y) (s y) (d₀ x) (s₀ x)
    change _ ≤ (Fintype.card ι:ℝ)*normalDensityError R (d y) (s y) (d₀ x) (s₀ x) at hdens
    have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
    have hc' := mul_lt_mul_of_pos_left hc hn
    have hemp := card_mul_integral_empiricalLaw y (f x)
    have ht := mul_le_mul_of_nonneg_left (htail y hy) hα
    have hsum : (∑ i, (f x (y i)+α*squareTail R₁ (y i))) =
        (∑ i, f x (y i))+α*∑ i, squareTail R₁ (y i) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    have hsmall : exp ((Fintype.card ι:ℝ)*ψ y)*productNormal (d y) (s y) y ≤ F x y := by
      dsimp only [F]
      rw [productNormal_eq_exp _ (hpos y hy),productNormal_eq_exp _ (hs₀ x hx),
        hsum,← exp_add,← exp_add,← exp_add]
      apply exp_le_exp.mpr
      nlinarith
    exact hsmall.trans (Finset.single_le_sum (fun a _ => hFnn a y) hx)
  have hsumI : Integrable (fun y => ∑ x ∈ C, F x y) := integrable_finsetSum C hFi
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, ∑ x ∈ C, F x y) :=
      (ofReal_integral_eq_lintegral_ofReal hsumI (ae_of_all _ (fun y => Finset.sum_nonneg (fun x _ => hFnn x y)))).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_finsetSum C hFi]
      calc
        _ ≤ ∑ _x ∈ C, exp ((Fintype.card ι:ℝ)*(r+ε-α*ν)) := Finset.sum_le_sum hnorm
        _ = _ := by simp

end SKGap

end
end
end
end
end
end
end
end
end

end OAI
