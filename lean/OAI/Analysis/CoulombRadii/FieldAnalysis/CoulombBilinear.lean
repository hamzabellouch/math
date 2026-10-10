import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.MeridianMap
import OAI.Analysis.CoulombRadii.FieldAnalysis.Rotation

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
namespace Coulomb
lemma fineKernel_continuous (b : ℝ) : Continuous (fineKernel b) := by
  have hs : Continuous (fun p : Space × Rotation => (p.2,p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hc := (rotated_flatKernel_continuous b).comp hs
  dsimp only [Function.comp_def] at hc
  have H := continuous_parametric_integral_of_continuous
    (μ := rotationMeasure) (f := fun x : Space => fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp)
    hc
    (s := univ) isCompact_univ
  change Continuous (fun x : Space => ∫ Q : Rotation, flatFineKernel b (rotationIsometry Q x).ofLp ∂rotationMeasure)
  simpa only [Measure.restrict_univ] using H

lemma flatFineKernel_neg (b : ℝ) (x : Fin 3 → ℝ) :
    flatFineKernel b (-x) = flatFineKernel b x := by simp [flatFineKernel]
lemma fineKernel_neg (b : ℝ) (x : Space) : fineKernel b (-x) = fineKernel b x := by
  unfold fineKernel
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun Q => by
    dsimp only
    rw [map_neg]
    exact flatFineKernel_neg b _)

lemma fineKernel_isometry (b : ℝ) (E : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    fineKernel b (E x) = fineKernel b x := by
  let U := Unitary.linearIsometryEquiv.symm E
  let T := Matrix.toEuclideanCLM (n:=Fin 3) (𝕜:=ℝ)
  let A : Matrix (Fin 3) (Fin 3) ℝ := T.symm U.val
  have hAE : T A = (E : Space →L[ℝ] Space) := by
    simp [A, U, Unitary.coe_symm_linearIsometryEquiv_apply]
  have hA : A ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    constructor
    · apply T.injective
      change T (star A*A) = T 1
      dsimp only [A]
      simpa only [map_mul, map_star, map_one, T.apply_symm_apply] using U.prop.1
    · apply T.injective
      change T (A*star A) = T 1
      dsimp only [A]
      simpa only [map_mul, map_star, map_one, T.apply_symm_apply] using U.prop.2
  have hdet : A.det = 1 ∨ A.det = -1 := by
    have H := (Matrix.det_of_mem_unitary hA).1
    simp only [star_trivial] at H
    rcases mul_self_eq_one_iff.mp H with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hdet with hdet | hdet
  · let Q : Rotation := ⟨A,hA,hdet⟩
    have hQ : rotationIsometry Q x = E x := by
      change T A x = E x
      rw [hAE]
      rfl
    rw [← hQ]
    exact fineKernel_rotation b Q x
  · have hnA : -A ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
      constructor
      · simpa only [star_neg, neg_mul_neg] using hA.1
      · simpa only [star_neg, neg_mul_neg] using hA.2
    have hnD : (-A).det = 1 := by norm_num [Matrix.det_neg, hdet]
    let Q : Rotation := ⟨-A,hnA,hnD⟩
    have hQ : rotationIsometry Q x = -(E x) := by
      change T (-A) x = -(E x)
      rw [map_neg, hAE]
      rfl
    rw [← fineKernel_neg b (E x), ← hQ]
    exact fineKernel_rotation b Q x

lemma fineKernel_radial (b : ℝ) {x y : Space} (h : ‖x‖ = ‖y‖) :
    fineKernel b x = fineKernel b y := by
  let E := (ℝ ∙ (x-y))ᗮ.reflection
  have hE : E x = y := Submodule.reflection_sub h
  rw [← hE, fineKernel_isometry]

lemma fineKernel_profile (b : ℝ) (x : Space) :
    fineKernel b x = fineKernel b (EuclideanSpace.single 0 ‖x‖) := by
  apply fineKernel_radial
  simp

lemma fineKernel_coulomb_integrable {b : ℝ} (hb : 0 < b) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*fineKernel b y) :=
  coulomb_convolution_integrable (fineKernel_integrable hb) (fineKernel_continuous b).measurable
    (fineKernel_nonneg b) (fineKernel_le hb) (by norm_num : (0:ℝ) < 1) x

lemma fineKernel_coulomb_le {b : ℝ} (hb : 0 < b) {x : Space} (hx : x ≠ 0) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) ≤ coulombKernel x := by
  simpa only [fineKernel_integral hb, mul_one] using
    radial_coulomb_integral_le (fineKernel_integrable hb) (fineKernel_continuous b).measurable
      (fineKernel_nonneg b) (fineKernel_le hb) (fineKernel_profile b) hx

lemma fineKernel_coulomb_eq {b : ℝ} (hb : 0 < b) {x : Space}
    (hx : Real.sqrt 3*b ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) = coulombKernel x := by
  have hR : 0 < Real.sqrt 3*b := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hb
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have hfs (y : Space) (hy : Real.sqrt 3*b < ‖y‖) : fineKernel b y = 0 := by
    apply fineKernel_eq_zero hb
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_nonneg (‖y‖-Real.sqrt 3*b)]
  simpa only [fineKernel_integral hb, mul_one] using
    radial_coulomb_integral_eq (fineKernel_integrable hb) (fineKernel_continuous b).measurable
      (fineKernel_nonneg b) (fineKernel_le hb) (fineKernel_profile b) hR.le hfs hx0 hx
noncomputable def coulombBilinear (f g : Space → ℝ) : ℝ :=
  ∫ p : Space × Space, f p.1*g p.2*coulombKernel (p.1-p.2)

lemma coulombBilinear_iterated {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    coulombBilinear f g = ∫ x, f x*(∫ y, coulombKernel (x-y)*g y) := by
  unfold coulombBilinear
  change (∫ p : Space × Space, f p.1*g p.2*coulombKernel (p.1-p.2) ∂volume.prod volume) = _
  rw [integral_prod _ (coulomb_pair_integrable hf hfm hg hgm hM)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ring))

lemma fineKernel_shift_integrable {b : ℝ} (hb : 0 < b) (a : Space) :
    Integrable (fun y => fineKernel b (y-a)) := (fineKernel_integrable hb).comp_sub_right a

lemma fineKernel_shift_integral {b : ℝ} (hb : 0 < b) (a : Space) :
    (∫ y, fineKernel b (y-a)) = 1 := by
  rw [integral_sub_right_eq_self, fineKernel_integral hb]

lemma fineKernel_shift_coulomb_integral {b : ℝ} (a x : Space) :
    (∫ y, coulombKernel (x-y)*fineKernel b (y-a)) =
      ∫ y, coulombKernel ((x-a)-y)*fineKernel b y := by
  rw [← integral_sub_right_eq_self (fun y => coulombKernel ((x-a)-y)*fineKernel b y) a]
  congr 1
  funext y
  congr 2
  abel

lemma fineKernel_coulomb_bound {b : ℝ} (hb : 0 < b) (x : Space) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) ≤ (2*Real.pi+1)/b := by
  have H := coulomb_convolution_bound (fineKernel_integrable hb) (fineKernel_continuous b).measurable
    (fineKernel_nonneg b) (fineKernel_le hb) hb x
  rw [fineKernel_integral hb] at H
  convert H using 1; field_simp

lemma fineKernel_pair_le {b : ℝ} (hb : 0 < b) {a c : Space} (hac : a ≠ c) :
    coulombBilinear (fun x => fineKernel b (x-a)) (fun x => fineKernel b (x-c)) ≤
      coulombKernel (a-c) := by
  have hi := fineKernel_shift_integrable hb
  have hm (v : Space) : Measurable (fun x => fineKernel b (x-v)) :=
    (fineKernel_continuous b).measurable.comp (by fun_prop)
  have hbnd (v x : Space) : ‖fineKernel b (x-v)‖ ≤ (b⁻¹)^3 := by
    rw [Real.norm_of_nonneg (fineKernel_nonneg b _)]
    exact fineKernel_le hb _
  rw [coulombBilinear_iterated (hi a) (hm a) (hi c) (hm c) (hbnd c)]
  simp_rw [fineKernel_shift_coulomb_integral]
  have hp := (coulomb_pair_integrable (hi a) (hm a) (hi c) (hm c) (hbnd c)).integral_prod_left
  have hip : Integrable (fun x => fineKernel b (x-a)*
      (∫ y, coulombKernel ((x-c)-y)*fineKernel b y)) := by
    apply hp.congr
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← fineKernel_shift_coulomb_integral c x, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring))
  have hik : Integrable (fun x => fineKernel b (x-a)*coulombKernel (x-c)) := by
    have h := coulomb_convolution_integrable (hi a) (hm a)
      (fun y => fineKernel_nonneg b (y-a)) (fun y => fineKernel_le hb (y-a))
      hb c
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => by dsimp only; unfold coulombKernel; rw [norm_sub_rev]; ring)
  calc
    _ ≤ ∫ x, fineKernel b (x-a)*coulombKernel (x-c) := by
      apply integral_mono_ae hip hik
      have hc : ∀ᵐ x : Space, x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hc] with x hx
      exact mul_le_mul_of_nonneg_left (fineKernel_coulomb_le hb (sub_ne_zero.mpr hx)) (fineKernel_nonneg b _)
    _ = ∫ x, coulombKernel ((c-a)-x)*fineKernel b x := by
      rw [← fineKernel_shift_coulomb_integral]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; unfold coulombKernel; rw [norm_sub_rev]; ring)
    _ ≤ coulombKernel (c-a) := fineKernel_coulomb_le hb (sub_ne_zero.mpr hac.symm)
    _ = _ := by unfold coulombKernel; rw [norm_sub_rev]

lemma fineKernel_pair_self_le {b : ℝ} (hb : 0 < b) (a : Space) :
    coulombBilinear (fun x => fineKernel b (x-a)) (fun x => fineKernel b (x-a)) ≤
      (2*Real.pi+1)/b := by
  have hi := fineKernel_shift_integrable hb a
  have hm : Measurable (fun x => fineKernel b (x-a)) :=
    (fineKernel_continuous b).measurable.comp (by fun_prop)
  have hbnd (x : Space) : ‖fineKernel b (x-a)‖ ≤ (b⁻¹)^3 := by
    rw [Real.norm_of_nonneg (fineKernel_nonneg b _)]
    exact fineKernel_le hb _
  rw [coulombBilinear_iterated hi hm hi hm hbnd]
  have hp := (coulomb_pair_integrable hi hm hi hm hbnd).integral_prod_left
  have hip : Integrable (fun x => fineKernel b (x-a)*
      (∫ y, coulombKernel (x-y)*fineKernel b (y-a))) := by
    apply hp.congr
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring))
  calc
    _ ≤ ∫ x, fineKernel b (x-a)*((2*Real.pi+1)/b) := by
      apply integral_mono hip (hi.mul_const _)
      intro x
      dsimp only
      rw [fineKernel_shift_coulomb_integral]
      exact mul_le_mul_of_nonneg_left (fineKernel_coulomb_bound hb _) (fineKernel_nonneg b _)
    _ = (2*Real.pi+1)/b := by rw [integral_mul_const, fineKernel_shift_integral hb, one_mul]

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
