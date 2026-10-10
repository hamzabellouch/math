import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
noncomputable def packetWindowed (g h : 𝓢(Space,ℂ)) (y : Space) : 𝓢(Space,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    ((SchwartzMap.compSubConstCLM ℂ y g).postcompCLM Complex.conjCLE.toContinuousLinearMap) h
lemma packetWindowed_apply (g h : 𝓢(Space,ℂ)) (y x : Space) :
    packetWindowed g h y x = conj (g (x-y))*h x := by
  unfold packetWindowed
  rw [SchwartzMap.smulLeftCLM_apply_apply
    ((SchwartzMap.compSubConstCLM ℂ y g).postcompCLM Complex.conjCLE.toContinuousLinearMap).hasTemperateGrowth]
  rfl
noncomputable def packetAnalysis (g h : 𝓢(Space,ℂ)) (y p : Space) : ℂ :=
  𝓕 (packetWindowed g h y) p
lemma packetAnalysis_integral (g h : 𝓢(Space,ℂ)) (y p : Space) :
    packetAnalysis g h y p = ∫ x : Space,
      Complex.exp ((-2*Real.pi*inner ℝ x p : ℝ)*Complex.I)*(conj (g (x-y))*h x) := by
  unfold packetAnalysis
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  simp only [packetWindowed_apply,smul_eq_mul]
lemma packetAnalysis_measurable (g h : 𝓢(Space,ℂ)) :
    StronglyMeasurable (fun yp : Space × Space => packetAnalysis g h yp.1 yp.2) := by
  simp only [packetAnalysis_integral]
  let k : (Space × Space) × Space → ℂ := fun z =>
    Complex.exp ((-2*Real.pi*inner ℝ z.2 z.1.2 : ℝ)*Complex.I)*
      (conj (g (z.2-z.1.1))*h z.2)
  have hk : Continuous k := by
    exact (((Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_snd.inner continuous_fst.snd)))).mul
      continuous_const).cexp).mul
        (((Complex.continuous_conj.comp (g.continuous.comp (continuous_snd.sub continuous_fst.fst)))).mul
          (h.continuous.comp continuous_snd))
  exact hk.stronglyMeasurable.integral_prod_right'
lemma packetAnalysis_momentum (g h : 𝓢(Space,ℂ)) (y : Space) :
    (∫ p : Space,‖packetAnalysis g h y p‖^2) =
      ∫ x : Space, ‖g (x-y)‖^2*‖h x‖^2 := by
  simp only [packetAnalysis]
  rw [SchwartzMap.integral_norm_sq_fourier]
  simp [packetWindowed_apply,mul_pow]
lemma packetAnalysis_momentum_integrable (g h : 𝓢(Space,ℂ)) (y : Space) :
    Integrable (fun p : Space => ‖packetAnalysis g h y p‖^2) :=
  (𝓕 (packetWindowed g h y)).memLp 2 volume |>.integrable_norm_pow (by norm_num)
lemma packetWindowed_joint_integrable (g h : 𝓢(Space,ℂ)) :
    Integrable (fun yx : Space × Space => ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2)
      (volume.prod volume) := by
  have hg : Integrable (fun x : Space => ‖g x‖^2) :=
    (g.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hh : Integrable (fun x : Space => ‖h x‖^2) :=
    (h.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hm : Continuous (fun yx : Space × Space => ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2) :=
    ((g.continuous.comp (continuous_snd.sub continuous_fst)).norm.pow 2).mul
      ((h.continuous.comp continuous_snd).norm.pow 2)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (hg.comp_sub_left x).mul_const (‖h x‖^2)),?_⟩
  change Integrable (fun x : Space => ∫ y : Space, ‖‖g (x-y)‖^2*‖h x‖^2‖)
  have hs (x : Space) : (∫ y : Space,‖g (x-y)‖^2) = ∫ y : Space,‖g y‖^2 :=
    integral_sub_left_eq_self (fun y : Space => ‖g y‖^2) volume x
  simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),integral_mul_const,hs]
  exact hh.const_mul _
lemma packetWindowed_joint_integral (g h : 𝓢(Space,ℂ)) :
    (∫ yx : Space × Space, ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2 ∂volume.prod volume) =
      (∫ x : Space,‖g x‖^2)*(∫ x : Space,‖h x‖^2) := by
  rw [integral_prod_symm _ (packetWindowed_joint_integrable g h)]
  have hs (x : Space) : (∫ y : Space,‖g (x-y)‖^2) = ∫ y : Space,‖g y‖^2 :=
    integral_sub_left_eq_self (fun y : Space => ‖g y‖^2) volume x
  simp only [integral_mul_const,hs,integral_const_mul]
lemma packetAnalysis_integrable (g h : 𝓢(Space,ℂ)) :
    Integrable (fun yp : Space × Space => ‖packetAnalysis g h yp.1 yp.2‖^2)
      (volume.prod volume) := by
  apply (integrable_prod_iff ((packetAnalysis_measurable g h).norm.pow 2).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (packetAnalysis_momentum_integrable g h),?_⟩
  change Integrable (fun y : Space => ∫ p : Space, ‖‖packetAnalysis g h y p‖^2‖)
  simp only [Real.norm_of_nonneg (sq_nonneg _),packetAnalysis_momentum]
  exact (packetWindowed_joint_integrable g h).integral_prod_left
lemma packetAnalysis_resolution (g h : 𝓢(Space,ℂ)) :
    (∫ yp : Space × Space,‖packetAnalysis g h yp.1 yp.2‖^2 ∂volume.prod volume) =
      (∫ x : Space,‖g x‖^2)*(∫ x : Space,‖h x‖^2) := by
  rw [integral_prod _ (packetAnalysis_integrable g h)]
  simp only [packetAnalysis_momentum]
  rw [←integral_prod _ (packetWindowed_joint_integrable g h)]
  exact packetWindowed_joint_integral g h
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
noncomputable def packetState (g : 𝓢(Space,ℂ)) (y p : Space) : 𝓢(Space,ℂ) :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 (SchwartzMap.compSubConstCLM ℂ y g)))
lemma packetState_apply (g : 𝓢(Space,ℂ)) (y p x : Space) :
    packetState g y p x = Complex.exp ((2*Real.pi*inner ℝ x p : ℝ)*Complex.I)*g (x-y) := by
  let h := SchwartzMap.compSubConstCLM ℂ y g
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (-(innerₗ Space)) (⇑(𝓕 h : 𝓢(Space,ℂ))) (-p)) x
  have ht' : 𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 h)) x =
      Real.fourierChar (inner ℝ p x) • 𝓕⁻ (𝓕 h) x := by
    have hh : ((𝓕 h : 𝓢(Space,ℂ)) ∘ fun v => v + -p) =
        (SchwartzMap.compSubConstCLM ℂ p (𝓕 h) : Space → ℂ) := by
      ext v
      simp [sub_eq_add_neg]
    rw [hh] at ht
    change 𝓕⁻ (⇑(SchwartzMap.compSubConstCLM ℂ p (𝓕 h))) x =
      Real.fourierChar (-inner ℝ (-p) x) • 𝓕⁻ (⇑(𝓕 h : 𝓢(Space,ℂ))) x at ht
    simp only [inner_neg_left,neg_neg] at ht
    simpa only [SchwartzMap.fourierInv_coe] using ht
  change 𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 h)) x = _
  rw [ht',FourierTransform.fourierInv_fourier_eq]
  simp [h,Circle.smul_def,Real.fourierChar_apply,real_inner_comm]
lemma packetState_norm (g : 𝓢(Space,ℂ)) (y p x : Space) :
    ‖packetState g y p x‖ = ‖g (x-y)‖ := by
  rw [packetState_apply,norm_mul,Complex.norm_exp]
  simp
lemma packetState_integral_norm_sq (g : 𝓢(Space,ℂ)) (y p : Space) :
    (∫ x : Space,‖packetState g y p x‖^2) = ∫ x : Space,‖g x‖^2 := by
  simp only [packetState_norm]
  exact integral_sub_right_eq_self (fun x : Space => ‖g x‖^2) y
lemma packetState_inner (g h : 𝓢(Space,ℂ)) (y p : Space) :
    inner ℂ ((packetState g y p).toLp 2 volume) (h.toLp 2 volume) = packetAnalysis g h y p := by
  rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume,packetAnalysis_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [packetState_apply,RCLike.inner_apply',starRingEnd_apply,map_mul,mul_assoc]
  congr 1
  change conj (Complex.exp _) = _
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

lemma packetAnalysis_continuous (g h : 𝓢(Space,ℂ)) :
    Continuous (fun yp : Space × Space => packetAnalysis g h yp.1 yp.2) := by
  simp only [packetAnalysis_integral]
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hC := SchwartzMap.norm_le_seminorm ℝ g
  apply MeasureTheory.continuous_of_dominated
    (bound := fun x : Space => C * ‖h x‖)
  · intro yp
    exact (((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const).cexp.mul
      ((Complex.continuous_conj.comp (g.continuous.comp (continuous_id.sub continuous_const))).mul
        h.continuous)).aestronglyMeasurable
  · intro yp
    filter_upwards [] with x
    simp only [norm_mul, Complex.norm_exp]
    have he : ((-2*Real.pi*inner ℝ x yp.2 : ℝ)*Complex.I : ℂ).re = 0 := by simp
    rw [he, Real.exp_zero, one_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hC (x-yp.1)) (norm_nonneg _)
  · exact h.integrable.norm.const_mul C
  · filter_upwards [] with x
    exact (((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_const.inner continuous_snd))).mul continuous_const).cexp.mul
      ((Complex.continuous_conj.comp (g.continuous.comp (continuous_const.sub continuous_fst))).mul
        continuous_const))
end Coulomb

end

end OAI
