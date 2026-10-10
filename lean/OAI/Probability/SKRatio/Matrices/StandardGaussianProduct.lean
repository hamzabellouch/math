import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian

theorem hasDerivAt_gaussianPDFReal (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal d s)
      (-(y - d) / (s : ℝ) * gaussianPDFReal d s y) y := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  unfold gaussianPDFReal
  convert! (((((hasDerivAt_id y).sub_const d).pow 2).neg.div_const
    (2 * (s : ℝ))).exp).const_mul (1 / sqrt (2 * π * (s : ℝ))) using 1
  · ext x
    simp only [one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

theorem integrable_gaussian_iff {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal d s) ↔ Integrable (fun y => gaussianPDFReal d s y * f y) := by
  rw [gaussianReal_of_var_ne_zero d hs,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF d s)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem gaussian_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    {f f' : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f' y) y)
    (hf : Integrable f (gaussianReal d s)) (hf' : Integrable f' (gaussianReal d s))
    (hyf : Integrable (fun y => (y - d) * f y) (gaussianReal d s)) :
    (∫ y, (y - d) * f y ∂gaussianReal d s) =
      (s : ℝ) * (∫ y, f' y ∂gaussianReal d s) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hfg := (integrable_gaussian_iff hs).mp hf
  have hf'g := (integrable_gaussian_iff hs).mp hf'
  have hyfg := (integrable_gaussian_iff hs).mp hyf
  have hder (y : ℝ) : HasDerivAt (fun y => gaussianPDFReal d s y * f y)
      (gaussianPDFReal d s y * f' y -
        (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) y := by
    convert! (hasDerivAt_gaussianPDFReal d hs y).mul (hd y) using 1
    ring
  have hii : Integrable (fun y => gaussianPDFReal d s y * f' y -
      (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) :=
    hf'g.sub (hyfg.div_const _)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder hii hfg
  rw [integral_sub hf'g (hyfg.div_const (s : ℝ)), integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs,
    integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  have he : (∫ y, gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ) =
      ∫ y, gaussianPDFReal d s y * f' y := by linarith
  have hm := (div_eq_iff hsp.ne').mp he
  nlinarith only [hm]

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  infer_instance

theorem continuous_insertNth {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℝ) :
    Continuous (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simp only [Fin.insertNth_apply_same]
    convert! (continuous_id : Continuous (fun x : ℝ => x)) using 1
  · intro k
    simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_const : Continuous (fun _ : ℝ => u k))

theorem gaussianProduct_coordinate_IBP {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hdf : Continuous df)
    (hfbound : ∀ x, ‖f x‖ ≤ C) (hdfbound : ∀ x, ‖df x‖ ≤ D)
    (hder : ∀ (u : Fin n → ℝ) (z : ℝ),
      HasDerivAt (fun z => f (i.insertNth z u)) (df (i.insertNth z u)) z) :
    (∫ x, x i * f x ∂standardGaussianProduct (n + 1)) =
      ∫ x, df x ∂standardGaussianProduct (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n + 1) → ℝ => x i * f x)
      (standardGaussianProduct (n + 1)) := by
    simpa only [mul_comm, standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.aestronglyMeasurable (ae_of_all _ hfbound)
  have hi' : Integrable df (standardGaussianProduct (n + 1)) :=
    Integrable.of_bound hdf.aestronglyMeasurable D (ae_of_all _ hdfbound)
  have hsplit (g : (Fin (n + 1) → ℝ) → ℝ)
      (hg : Integrable g (standardGaussianProduct (n + 1))) :
      (∫ x, g x ∂standardGaussianProduct (n + 1)) =
        ∫ u, ∫ z, g (i.insertNth z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) :=
      hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g, integral_prod _ hi2]
    rw [integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi, hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Fin.insertNth_apply_same]
  have hfu : Integrable (fun z => f (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hf.comp (continuous_insertNth i u)).aestronglyMeasurable C
      (ae_of_all _ (fun z => hfbound _))
  have hdfu : Integrable (fun z => df (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hdf.comp (continuous_insertNth i u)).aestronglyMeasurable D
      (ae_of_all _ (fun z => hdfbound _))
  have hzfu : Integrable (fun z => z * f (i.insertNth z u)) (gaussianReal 0 1) := by
    simpa only [mul_comm, id_eq, Function.comp_def] using (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul
      (hf.comp (continuous_insertNth i u)).aestronglyMeasurable
      (ae_of_all _ (fun z => hfbound _))
  simpa only [NNReal.coe_one, sub_zero, one_mul] using
    gaussian_integration_by_parts (d := 0) (s := 1) one_ne_zero (hder u) hfu hdfu
      (by simpa only [sub_zero] using hzfu)

end SKRatioGaussian

open Filter
open scoped Topology

end
end
end

end OAI
